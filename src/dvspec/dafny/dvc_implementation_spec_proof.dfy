include "commons.dfy"
include "dvc_spec.dfy"

abstract module DVCNode_Implementation_Proofs refines DVCNode_Implementation
{
    import opened DVCNode_Spec
    import opened DVCNode_Externs = DVCNode_Externs_Proofs

    export PublicInterface...
        reveals *
        // provides 
        //         toDVCNodeState,
        //         f_resend_attestation_share,
        //         toDVCNodeStateAndOuputs,
        //         Outputs,
        //         getEmptyOuputs,
        //         f_att_consensus_decided,
        //         f_serve_attestation_duty,
        //         f_listen_for_new_imported_blocks,
        //         f_listen_for_attestation_shares,
        //         f_next,
        //         Event
        // reveals
        //         DVCNodeState,
        //         DVCNodeStateAndOuputs
        // provides
        //         DVCNode.network,
        //         DVCNode.att_consensus, 
        //         DVCNode.bn,
        //         DVCNode.current_attesation_duty
    // export reveals *
    // export 
    //     provides Types, DVCNode_Implementation_Helpers, DVCNode_Externs
    //     reveals DVCNode, toDVCNodeState
    //     provides 
    //             DVCNode.serve_attestation_duty, 
    //             DVCNode.att_consensus_decided, 
    //             DVCNode.listen_for_attestation_duty_shares,
    //             DVCNode.listen_for_new_imported_blocks,
    //             DVCNode.resend_attestation_share

    function toDVCNodeState(n: DVCNode): DVCNodeState
    reads n, n.bn, n.rs
    {
        DVCNodeState(
            current_attesation_duty := n.current_attesation_duty,
            attestation_duties_queue := n.attestation_duties_queue,
            attestation_slashing_db := n.attestation_slashing_db,
            attestation_shares_db := n.attestation_shares_db,
            attestation_share_to_broadcast := n.attestation_share_to_broadcast,
            construct_signed_attestation_signature := n.construct_signed_attestation_signature,
            dv_pubkey := n.dv_pubkey,
            future_att_consensus_instances_already_decided := n.future_att_consensus_instances_already_decided,
            bn := toBNState(n.bn),
            rs := toRSState(n.rs)
        )
    }

    function seqToSet<T>(s: seq<T>): (r: set<T>)
    {
        set e | e in s
    }

    function seqMinusToSet<T>(s1: seq<T>, s2: seq<T>): set<T>
    // requires s2 <= s1 
    // ensures seqMinus(s1, s2) + s2 == s1
    {
        set i | |s2| <= i < |s1| :: s1[i]
    }

    function seqMinusToOptional<T>(s1: seq<T>, s2: seq<T>): Optional<T>
    requires s2 <= s1 
    requires |s1| <= |s2| + 1
    {
        if s1 == s2 then
            None 
        else
            Some(s1[|s2|])
    }






    twostate predicate onlyOneMaxConsensusCommandAndSubmittedAttestation(n: DVCNode)
    reads n, n.att_consensus, n.bn
    {
        && |n.att_consensus.consensus_commands_sent| <= |old(n.att_consensus.consensus_commands_sent)| + 1
        && |n.bn.attestations_submitted| <= |old(n.bn.attestations_submitted)| + 1
    }

    twostate function getOutputs(n: DVCNode): (o: Outputs)
    reads n, n.network, n.att_consensus, n.bn
    {
        Outputs(
            att_shares_sent :=  seqMinusToSet(n.network.att_shares_sent, old(n.network.att_shares_sent)),
            att_consensus_commands_sent := seqMinusToSet(n.att_consensus.consensus_commands_sent, old(n.att_consensus.consensus_commands_sent)),
            attestations_submitted := seqMinusToSet(n.bn.attestations_submitted, old(n.bn.attestations_submitted))
        )
    }

    

    twostate function toDVCNodeStateAndOuputs(n: DVCNode): DVCNodeStateAndOuputs
    reads n, n.network, n.att_consensus, n.bn, n.rs
    {
        DVCNodeStateAndOuputs(
            state := toDVCNodeState(n),
            outputs := getOutputs(n)
        )
    }

 




    class DVCNode...
    {

        method update_attestation_slashing_db...
        ensures f_update_attestation_slashing_db(old(toDVCNodeState(this)).attestation_slashing_db, attestation_data, attestation_duty_pubkey) == this.attestation_slashing_db;  

        method serve_attestation_duty...
        ensures f_serve_attestation_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this);
        {
            ...;
            assert f_serve_attestation_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this);
        }

        method check_for_next_queued_duty...
        ensures f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
        {
            if...
            {
                if...
                {
                    ...;
                    assert f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
                }
                else
                {
                    ...;
                    assert f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
                }
            }
            else
            {
                assert f_check_for_next_queued_duty(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
            }

        }        

        method start_next_duty...
        ensures f_start_next_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this);
        {
            ...;
            assert f_start_next_duty(old(toDVCNodeState(this)), attestation_duty) == toDVCNodeStateAndOuputs(this);
        }

        method att_consensus_decided...
        ensures old(this.current_attesation_duty).isPresent() ==> f_att_consensus_decided(old(toDVCNodeState(this)), id, decided_attestation_data) == toDVCNodeStateAndOuputs(this);
        {
            ...;
            if old(this.current_attesation_duty).isPresent()
            {
                assert f_att_consensus_decided(old(toDVCNodeState(this)), id, decided_attestation_data) == toDVCNodeStateAndOuputs(this);
            }
        }

        method listen_for_attestation_shares...
        ensures f_listen_for_attestation_shares(old(toDVCNodeState(this)), attestation_share) == toDVCNodeStateAndOuputs(this);
        {
            ...;
        }

        lemma lll<T, T2>(s: seq<T>, p: T -> bool, f: T -> T2, i: nat)
        requires |s| > 0
        requires i <= |s| - 1;
        requires !p(s[i])
        ensures
            var S := set a | a in s[..i] && p(a) :: f(a);
            var S2  := set a | a in s[..i+1] && p(a) :: f(a); 
            S == S2       
        {
            

            var S := set a | a in s[..i] && p(a) :: f(a);
            var S2  := set a | a in s[..i+1] && p(a) :: f(a);

            assert S == S2;
        }



        // lemma l2(block: BeaconBlock, old_future_att_consensus_instances_already_decided: set<Slot>, old_process: DVCNodeState)
        // requires                 
        // var new_att := future_att_consensus_instances_already_decided - old_future_att_consensus_instances_already_decided; 
        // block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //     new_att == xxx(process, block, valIndex, i);  
        // {                

        //         var a := block.body.attestations[i];
        //         var committee :- bn.get_epoch_committees(block.body.state_root, a.data.index);

                
        //         if
        //         // && a.data.slot == process.attestation_duty.slot 
        //         // && a.data.index == process.attestation_duty.committee_index
        //         && valIndex.Some?
        //         && valIndex.v in committee
        //         && var i:nat :| i < |committee| && committee[i] == valIndex.v;
        //         && i < |a.aggregation_bits|
        //         && a.aggregation_bits[i]
        //         && (current_attesation_duty.isPresent() ==> a.data.slot >= current_attesation_duty.safe_get().slot)
        //         {
        //             future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided + {a.data.slot};
        //         }
        //         else
        //         {
        //             assert 
        //                 var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //                 var process := old(toDVCNodeState(this));
        //                 block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //                     new_att == xxx(process, block, valIndex, i);   

        //             assert 
        //                 var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //                 var process := old(toDVCNodeState(this));
        //                 block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //                     new_att == xxx(process, block, valIndex, i + 1);                                                   
        //         }            
        // }

        method listen_for_new_imported_blocks...
        ensures block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toDVCNodeState(this)), block) == toDVCNodeStateAndOuputs(this);
        {
            ...;
            while...
                invariant 0 <= i <= |block.body.attestations|
                invariant  block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
                    future_att_consensus_instances_already_decided == 
                    old(future_att_consensus_instances_already_decided) + xxx(old(toDVCNodeState(this)), block, valIndex, i); 
                    
                invariant toDVCNodeState(this) == old(toDVCNodeState(this)).(
                    future_att_consensus_instances_already_decided := toDVCNodeState(this).future_att_consensus_instances_already_decided
                )
                invariant toDVCNodeStateAndOuputs(this).outputs == getEmptyOuputs();            
            {

            }
        }

        // method listen_for_new_imported_blocks...
        // ensures block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toDVCNodeState(this)), block) == toDVCNodeStateAndOuputs(this);
        // {
        //     var valIndex :- bn.get_validator_index(block.body.state_root, dv_pubkey);
        //     var i := 0;

        //     while i < |block.body.attestations|
        //         invariant 0 <= i <= |block.body.attestations|
        //         invariant 
        //                         var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //         block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //             future_att_consensus_instances_already_decided == old(future_att_consensus_instances_already_decided) + xxx(old(toDVCNodeState(this)), block, valIndex, i); 

        //         invariant current_attesation_duty == old(toDVCNodeState(this)).current_attesation_duty;
        //         invariant toDVCNodeState(this) == old(toDVCNodeState(this)).(
        //             future_att_consensus_instances_already_decided := toDVCNodeState(this).future_att_consensus_instances_already_decided
        //         )
        //         invariant toDVCNodeStateAndOuputs(this).outputs == getEmptyOuputs();
        //     {
        //         var a := block.body.attestations[i];
        //         var committee :- bn.get_epoch_committees(block.body.state_root, a.data.index);
                                 
        //         if
        //         // && a.data.slot == process.attestation_duty.slot 
        //         // && a.data.index == process.attestation_duty.committee_index
        //         && valIndex.Some?
        //         && valIndex.v in committee
        //         && var i:nat :| i < |committee| && committee[i] == valIndex.v;
        //         && i < |a.aggregation_bits|
        //         && a.aggregation_bits[i]
        //         && (current_attesation_duty.isPresent() ==> a.data.slot >= current_attesation_duty.safe_get().slot)
        //         {
        //             future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided + {a.data.slot};                     
        //         }

        //         i := i + 1;
        //     }                           

        //     if current_attesation_duty.isPresent() && current_attesation_duty.safe_get().slot in future_att_consensus_instances_already_decided
        //     {
        //         att_consensus.stop(current_attesation_duty.safe_get().slot);
        //         check_for_next_queued_duty();
        //     } 

        //     assert block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toDVCNodeState(this)), block) == toDVCNodeStateAndOuputs(this);
        // }        

        // method listen_for_new_imported_blocks...
        // // ensures block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toDVCNodeState(this)), block) == toDVCNodeStateAndOuputs(this);
        // {
        //     ...;

        //     while...
        //         invariant 0 <= i <= |block.body.attestations|
        //         // invariant 
        //         // var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //         // var process := old(toDVCNodeState(this));
        //         // block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //         //     new_att == 
        //         //         set a |
        //         //             && a in block.body.attestations[..i]
        //         //             // && a.data.slot == process.attestation_duty.slot 
        //         //             // && a.data.index == process.attestation_duty.committee_index
        //         //             && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
        //         //             && valIndex.Some?
        //         //             && valIndex.v in committee
        //         //             && var i:nat :| i < |committee| && committee[i] == valIndex.v;
        //         //             && i < |a.aggregation_bits|
        //         //             && a.aggregation_bits[i]
        //         //             && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)
        //         //          ::
        //         //             a.data.slot;
        //     {
        //         assume                 
        //         var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //         var process := old(toDVCNodeState(this));
        //         block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //             new_att == 
        //                 set a |
        //                     && a in block.body.attestations[..i]
        //                     // && a.data.slot == process.attestation_duty.slot 
        //                     // && a.data.index == process.attestation_duty.committee_index
        //                     && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
        //                     && valIndex.Some?
        //                     && valIndex.v in committee
        //                     && var i:nat :| i < |committee| && committee[i] == valIndex.v;
        //                     && i < |a.aggregation_bits|
        //                     && a.aggregation_bits[i]
        //                     && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)
        //                  ::
        //                     a.data.slot;                
        //         ...;

        //         if...
        //         {

        //             assert                 
        //             var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //             var process := old(toDVCNodeState(this));
        //             block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //                 new_att == 
        //                     set a |
        //                         && a in block.body.attestations[..i]
        //                         // && a.data.slot == process.attestation_duty.slot 
        //                         // && a.data.index == process.attestation_duty.committee_index
        //                         && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
        //                         && valIndex.Some?
        //                         && valIndex.v in committee
        //                         && var i:nat :| i < |committee| && committee[i] == valIndex.v;
        //                         && i < |a.aggregation_bits|
        //                         && a.aggregation_bits[i]
        //                         && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)
        //                     ::
        //                         a.data.slot;                    
        //             ...;
        //         }
        //         else
        //         {
  
        //         }
        //         ...;
        //     }
        //     ...;
        // }

        method resend_attestation_share...
        ensures f_resend_attestation_share(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this)
        {
            ...;
            assert  f_resend_attestation_share(old(toDVCNodeState(this))) == toDVCNodeStateAndOuputs(this);
        }
    }
}