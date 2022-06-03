include "dvc4.dfy"

module CoVNode_Externs_Proofs refines CoVNode_Externs
{
    function {:axiom} bn_get_fork_version(slot: Slot): Version

    function {:axiom} bn_get_validator_index(bnState: BNState, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} bn_get_epoch_committees(bnState: BNState, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks

    datatype BNState = BNState(
        state_roots_of_imported_blocks: set<Root>   
    )

    function toBNState(bn: BeaconNode): BNState
    reads bn
    {
        BNState(
            state_roots_of_imported_blocks := bn.state_roots_of_imported_blocks
        )
    }

    class BeaconNode...
    {
        method get_fork_version...
        ensures bn_get_fork_version(s) == v

        method get_validator_index...
        ensures state_id in this.state_roots_of_imported_blocks ==> bn_get_validator_index(toBNState(this),state_id, validator_id) == vi

        method get_epoch_committees...
        ensures state_id in this.state_roots_of_imported_blocks ==> bn_get_epoch_committees(toBNState(this), state_id, index) == sv
    }

    function {:axiom} rs_sign_attestation(
        attestation_data: AttestationData, 
        fork_version: Version, 
        signing_root: Root,
        pubkey: BLSPubkey
    ): BLSSignature
    requires signing_root == compute_attestation_signing_root(attestation_data, fork_version)

    lemma {:axiom} rs_attestation_sign_and_verification_propetries<T>()
    ensures forall attestation_data, fork_version, signing_root, pubkey |
                    rs_sign_attestation.requires(attestation_data, fork_version, signing_root, pubkey) ::
                    verify_bls_siganture(
                        signing_root,
                        rs_sign_attestation(attestation_data, fork_version, signing_root, pubkey),
                        pubkey
                    )
    ensures forall signing_root, signature, pubkey ::
        verify_bls_siganture(signing_root, signature, pubkey) <==>
            exists attestation_data, fork_version ::
            && rs_sign_attestation.requires(attestation_data, fork_version, signing_root, pubkey)
            && signature == rs_sign_attestation(attestation_data, fork_version, signing_root, pubkey)

    ensures forall ad1, fv1, sr1, pk1, ad2, fv2, sr2, pk2 ::
            && rs_sign_attestation.requires(ad1, fv1, sr1, pk1)
            && rs_sign_attestation.requires(ad2, fv2, sr2, pk2)
            && rs_sign_attestation(ad1, fv1, sr1, pk1) == rs_sign_attestation(ad2, fv2, sr2, pk2) 
            ==>
            && sr1 == sr2 
            && pk1 == pk2 


    class RemoteSigner...
    {
        method sign_attestation...
        ensures signing_root == compute_attestation_signing_root(attestation_data, fork_version)
        ensures rs_sign_attestation(attestation_data, fork_version, signing_root, this.pubkey) == s
    }

}

module CoVNode_Implementation_Proofs refines CoVNode_Implementation
{
    import opened CoVNode_Externs = CoVNode_Externs_Proofs

    export PublicInterface...
        provides 
                toCoVNodeState,
                f_resend_attestation_share,
                toCoVNodeStateAndOuputs,
                Outputs,
                getEmptyOuputs,
                f_att_consensus_decided,
                f_serve_attestation_duty,
                f_listen_for_new_imported_blocks,
                f_listen_for_attestation_duty_shares
        reveals
                CoVNodeState,
                CoVNodeStateAndOuputs
        provides
                CoVNode.network,
                CoVNode.att_consensus, 
                CoVNode.bn,
                CoVNode.current_attesation_duty
    // export reveals *
    // export 
    //     provides Types, CoVNode_Implementation_Helpers, CoVNode_Externs
    //     reveals CoVNode, toCoVNodeState
    //     provides 
    //             CoVNode.serve_attestation_duty, 
    //             CoVNode.att_consensus_decided, 
    //             CoVNode.listen_for_attestation_duty_shares,
    //             CoVNode.listen_for_new_imported_blocks,
    //             CoVNode.resend_attestation_share

    datatype CoVNodeState = CoVNodeState(
        current_attesation_duty: Optional<AttestationDuty>,
        attestation_duties_queue: seq<AttestationDuty>,
        attestation_slashing_db: AttestationSlashingDB,
        attestation_shares_db: AttestationSignatureShareDB,
        attestation_share_to_broadcast: Optional<AttestationShare>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        // TODO: Note difference with spec.py
        dv_pubkey: BLSPubkey,
        future_att_consensus_instances_already_decided: set<Slot>,
        cov_pubkey: BLSPubkey,
        bn: BNState    
    )

    function toCoVNodeState(n: CoVNode): CoVNodeState
    reads n, n.bn
    {
        CoVNodeState(
            current_attesation_duty := n.current_attesation_duty,
            attestation_duties_queue := n.attestation_duties_queue,
            attestation_slashing_db := n.attestation_slashing_db,
            attestation_shares_db := n.attestation_shares_db,
            attestation_share_to_broadcast := n.attestation_share_to_broadcast,
            construct_signed_attestation_signature := n.construct_signed_attestation_signature,
            dv_pubkey := n.dv_pubkey,
            future_att_consensus_instances_already_decided := n.future_att_consensus_instances_already_decided,
            cov_pubkey := n.rs.pubkey,
            bn := toBNState(n.bn)
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

    datatype Outputs = Outputs(
        att_shares_sent: set<AttestationShare>,
        att_consensus_commands_sent: set<CoVNode_Externs.ConsensuCommand>,
        attestations_submitted: set<Attestation>
    )


    function getEmptyOuputs(): Outputs
    {
        Outputs(
            {},
            {},
            {}
        )
    }

    twostate function getOutputs(n: CoVNode): (o: Outputs)
    reads n, n.network, n.att_consensus, n.bn
    {
        Outputs(
            att_shares_sent :=  seqMinusToSet(n.network.att_shares_sent, old(n.network.att_shares_sent)),
            att_consensus_commands_sent := seqMinusToSet(n.att_consensus.consensus_commands_sent, old(n.att_consensus.consensus_commands_sent)),
            attestations_submitted := seqMinusToSet(n.bn.attestations_submitted, old(n.bn.attestations_submitted))
        )
    }

    datatype CoVNodeStateAndOuputs = CoVNodeStateAndOuputs(
        state: CoVNodeState,
        outputs: Outputs
    )

    twostate function toCoVNodeStateAndOuputs(n: CoVNode): CoVNodeStateAndOuputs
    reads n, n.network, n.att_consensus, n.bn
    {
        CoVNodeStateAndOuputs(
            state := toCoVNodeState(n),
            outputs := getOutputs(n)
        )
    }

    function f_update_attestation_slashing_db(attestation_slashing_db: AttestationSlashingDB, attestation_data: AttestationData, attestation_duty_pubkey: BLSPubkey): AttestationSlashingDB     
    {
        // assert not is_slashable_attestation_data(attestation_slashing_db, attestation_data, pubkey)
        // TODO: Is the following required given that each co-validator only handles one pubkey?
        // slashing_db_data = get_slashing_db_data_for_pubkey(attestation_slashing_db, pubkey)
        var slashing_db_attestation := SlashingDBAttestation(
                                            source_epoch := attestation_data.source.epoch,
                                            target_epoch := attestation_data.target.epoch,
                                            signing_root := hash_tree_root(attestation_data));
        
        attestation_slashing_db + {slashing_db_attestation}
    }   

    function f_serve_attestation_duty(
        process: CoVNodeState,
        attestation_duty: AttestationDuty
    ): CoVNodeStateAndOuputs
    {
        f_check_for_next_queued_duty(
            process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty]
            )
        )
    }    

    function f_check_for_next_queued_duty(process: CoVNodeState): CoVNodeStateAndOuputs
    decreases process.attestation_duties_queue
    {
        if process.attestation_duties_queue != [] then
            
                if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided then
                    f_check_for_next_queued_duty(process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    ))
                else
                    f_start_next_duty(process, process.attestation_duties_queue[0])
                
        else 
            CoVNodeStateAndOuputs(
                state := process,
                outputs := getEmptyOuputs()
            )

    }         

    function f_start_next_duty(process: CoVNodeState, attestation_duty: AttestationDuty): CoVNodeStateAndOuputs
    {
        CoVNodeStateAndOuputs(
            state :=  process.(
                        attestation_shares_db := map[],
                        attestation_share_to_broadcast := None,
                        current_attesation_duty := Some(attestation_duty)
            ),
            outputs := getEmptyOuputs().(
                att_consensus_commands_sent := {Start(attestation_duty.slot)}
            )
        )        
    }      

    function get_aggregation_bits(
        index: nat
    ): seq<bool>
    {
        seq(index, i => if i + 1 == index then true else false)
    } 

    function f_att_consensus_decided(
        process: CoVNodeState,
        decided_attestation_data: AttestationData
    ): CoVNodeStateAndOuputs
    requires process.current_attesation_duty.isPresent()
    {
        var local_current_attestation_duty := process.current_attesation_duty.safe_get();
        var attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, decided_attestation_data, local_current_attestation_duty.pubkey);

        var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
        var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
        var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, process.cov_pubkey);
        // TODO: What is attestation_signature_share.aggregation_bits?
        var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature :=attestation_signature_share
            ); 

        CoVNodeStateAndOuputs(
            state := process.(
                attestation_share_to_broadcast := Some(attestation_with_signature_share)
            ),
            outputs := getEmptyOuputs().(
                att_shares_sent := {attestation_with_signature_share}
            )
        )         
    }    

    function f_listen_for_attestation_duty_shares(
        process: CoVNodeState,
        attestation_share: AttestationShare
    ): CoVNodeStateAndOuputs
    {
        var k := (attestation_share.data, attestation_share.aggregation_bits);

        var newProcess := process.(
            attestation_shares_db := 
                process.attestation_shares_db[k := 
                                        getOrDefault(process.attestation_shares_db, k, {}) + 
                                        {attestation_share}
                                    ]
        );

                    
        if process.construct_signed_attestation_signature(newProcess.attestation_shares_db[k]).isPresent() then
        
            var aggregated_attestation := 
                    Attestation(
                        aggregation_bits := attestation_share.aggregation_bits,
                        data := attestation_share.data,
                        signature := process.construct_signed_attestation_signature(newProcess.attestation_shares_db[k]).safe_get()
                    );

            CoVNodeStateAndOuputs(
                state := newProcess,
                outputs := getEmptyOuputs().(
                    attestations_submitted := {aggregated_attestation} 
                )
            ) 
        else 
            CoVNodeStateAndOuputs(
                state := newProcess,
                outputs := getEmptyOuputs()
            ) 
    }
 
        function xxx(
            process: CoVNodeState,
            block: BeaconBlock,
            valIndex: Optional<ValidatorIndex>,
            i: nat
        ) : (new_att: set<Slot>)
        requires i <= |block.body.attestations|
        requires block.body.state_root in process.bn.state_roots_of_imported_blocks
        {            
            set a |
                    && a in block.body.attestations[..i]
                    && isMyAttestation(a, process, block, valIndex)
                    // && a.data.slot == process.attestation_duty.slot 
                    // && a.data.index == process.attestation_duty.committee_index
                    // && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
                    // && valIndex.Some?
                    // && valIndex.v in committee
                    // && var i:nat :| i < |committee| && committee[i] == valIndex.v;
                    // && i < |a.aggregation_bits|
                    // && a.aggregation_bits[i]
                    // && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)
                ::
                    a.data.slot
        }    

        // function xxxa(
        //     process: CoVNodeState,
        //     block: BeaconBlock,
        //     valIndex: Optional<ValidatorIndex>
        // ) : (new_att: set<Slot>)
        // requires block.body.state_root in process.bn.state_roots_of_imported_blocks
        // {            
        //     set a |
        //             && a in block.body.attestations
        //             // && isMyAttestation(a, process, block, valIndex)
        //             // && a.data.slot == process.attestation_duty.slot 
        //             // && a.data.index == process.attestation_duty.committee_index
        //             && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
        //             && valIndex.Some?
        //             && valIndex.v in committee
        //             && var i:nat :| i < |committee| && committee[i] == valIndex.v;
        //             && i < |a.aggregation_bits|
        //             && a.aggregation_bits[i]
        //             && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)
        //         ::
        //             a.data.slot
        // }  

        // lemma lxxxx(process: CoVNodeState,
        //     block: BeaconBlock,
        //     valIndex: Optional<ValidatorIndex>)
        //     requires block.body.state_root in process.bn.state_roots_of_imported_blocks
        // ensures xxx(process, block, valIndex, |block.body.attestations|) == xxxa(process, block, valIndex)
        // {
        //     assert block.body.attestations[..|block.body.attestations|] == block.body.attestations;
        // }           

        predicate isMyAttestation(
            a: Attestation,
            process: CoVNodeState,
            block: BeaconBlock,
            valIndex: Optional<ValidatorIndex>
        )
        {
                && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
                && valIndex.Some?
                && valIndex.v in committee
                && var i:nat :| i < |committee| && committee[i] == valIndex.v;
                && i < |a.aggregation_bits|
                && a.aggregation_bits[i]
                && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)            
        }

    function f_listen_for_new_imported_blocks(
        process: CoVNodeState,
        block: BeaconBlock
    ): CoVNodeStateAndOuputs
    requires block.body.state_root in process.bn.state_roots_of_imported_blocks
    {
        var valIndex := bn_get_validator_index(process.bn, block.body.state_root, process.dv_pubkey);
         
        var s := set a |
                && a in block.body.attestations
                && isMyAttestation(a, process, block, valIndex)
                // && a.data.slot == process.attestation_duty.slot 
                // && a.data.index == process.attestation_duty.committee_index
                // && var committee := bn_get_epoch_committees(process.bn, block.body.state_root, a.data.index);
                // && valIndex.Some?
                // && valIndex.v in committee
                // && var i:nat :| i < |committee| && committee[i] == valIndex.v;
                // && i < |a.aggregation_bits|
                // && a.aggregation_bits[i]
                // && (process.current_attesation_duty.isPresent() ==> a.data.slot >= process.current_attesation_duty.safe_get().slot)
            ::
                a.data.slot;

        var newProces := process.(
            future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided + s
        );

        if process.current_attesation_duty.isPresent() && process.current_attesation_duty.safe_get().slot in process.future_att_consensus_instances_already_decided then
            // Stop(current_attesation_duty.safe_get().slot);
            var r := f_check_for_next_queued_duty(newProces);
            CoVNodeStateAndOuputs(
                state := r.state,
                outputs := r.outputs.(
                    att_consensus_commands_sent := r.outputs.att_consensus_commands_sent + {Stop(process.current_attesation_duty.safe_get().slot)}
                )
            )
        else
            CoVNodeStateAndOuputs(
                state := newProces,
                outputs := getEmptyOuputs()
            )
    }    
  
    function f_resend_attestation_share(
        process: CoVNodeState
    ): CoVNodeStateAndOuputs
    {
        CoVNodeStateAndOuputs(
            state := process,
            outputs := getEmptyOuputs().(
                att_shares_sent :=
                    if process.attestation_share_to_broadcast.isPresent() then
                        {process.attestation_share_to_broadcast.safe_get()}
                    else
                        {}
                    )
        )

    }    

    class CoVNode...
    {

        method update_attestation_slashing_db...
        ensures f_update_attestation_slashing_db(old(toCoVNodeState(this)).attestation_slashing_db, attestation_data, attestation_duty_pubkey) == this.attestation_slashing_db;  

        method serve_attestation_duty...
        ensures f_serve_attestation_duty(old(toCoVNodeState(this)), attestation_duty) == toCoVNodeStateAndOuputs(this);
        {
            ...;
            assert f_serve_attestation_duty(old(toCoVNodeState(this)), attestation_duty) == toCoVNodeStateAndOuputs(this);
        }

        method check_for_next_queued_duty...
        ensures f_check_for_next_queued_duty(old(toCoVNodeState(this))) == toCoVNodeStateAndOuputs(this);
        {
            if...
            {
                if...
                {
                    ...;
                    assert f_check_for_next_queued_duty(old(toCoVNodeState(this))) == toCoVNodeStateAndOuputs(this);
                }
                else
                {
                    ...;
                    assert f_check_for_next_queued_duty(old(toCoVNodeState(this))) == toCoVNodeStateAndOuputs(this);
                }
            }
            else
            {
                assert f_check_for_next_queued_duty(old(toCoVNodeState(this))) == toCoVNodeStateAndOuputs(this);
            }

        }        

        method start_next_duty...
        ensures f_start_next_duty(old(toCoVNodeState(this)), attestation_duty) == toCoVNodeStateAndOuputs(this);
        {
            ...;
            assert f_start_next_duty(old(toCoVNodeState(this)), attestation_duty) == toCoVNodeStateAndOuputs(this);
        }

        method att_consensus_decided...
        ensures old(this.current_attesation_duty).isPresent() ==> f_att_consensus_decided(old(toCoVNodeState(this)), decided_attestation_data) == toCoVNodeStateAndOuputs(this);
        {
            ...;
            if old(this.current_attesation_duty).isPresent()
            {
                assert f_att_consensus_decided(old(toCoVNodeState(this)), decided_attestation_data) == toCoVNodeStateAndOuputs(this);
            }
        }

        method listen_for_attestation_duty_shares...
        ensures f_listen_for_attestation_duty_shares(old(toCoVNodeState(this)), attestation_share) == toCoVNodeStateAndOuputs(this);
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



        // lemma l2(block: BeaconBlock, old_future_att_consensus_instances_already_decided: set<Slot>, old_process: CoVNodeState)
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
        //                 var process := old(toCoVNodeState(this));
        //                 block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //                     new_att == xxx(process, block, valIndex, i);   

        //             assert 
        //                 var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //                 var process := old(toCoVNodeState(this));
        //                 block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //                     new_att == xxx(process, block, valIndex, i + 1);                                                   
        //         }            
        // }

        method listen_for_new_imported_blocks...
        ensures block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toCoVNodeState(this)), block) == toCoVNodeStateAndOuputs(this);
        {
            ...;
            while...
                invariant 0 <= i <= |block.body.attestations|
                invariant  block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
                    future_att_consensus_instances_already_decided == 
                    old(future_att_consensus_instances_already_decided) + xxx(old(toCoVNodeState(this)), block, valIndex, i); 
                    
                invariant toCoVNodeState(this) == old(toCoVNodeState(this)).(
                    future_att_consensus_instances_already_decided := toCoVNodeState(this).future_att_consensus_instances_already_decided
                )
                invariant toCoVNodeStateAndOuputs(this).outputs == getEmptyOuputs();            
            {

            }
        }

        // method listen_for_new_imported_blocks...
        // ensures block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toCoVNodeState(this)), block) == toCoVNodeStateAndOuputs(this);
        // {
        //     var valIndex :- bn.get_validator_index(block.body.state_root, dv_pubkey);
        //     var i := 0;

        //     while i < |block.body.attestations|
        //         invariant 0 <= i <= |block.body.attestations|
        //         invariant 
        //                         var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //         block.body.state_root in old(bn.state_roots_of_imported_blocks) ==>
        //             future_att_consensus_instances_already_decided == old(future_att_consensus_instances_already_decided) + xxx(old(toCoVNodeState(this)), block, valIndex, i); 

        //         invariant current_attesation_duty == old(toCoVNodeState(this)).current_attesation_duty;
        //         invariant toCoVNodeState(this) == old(toCoVNodeState(this)).(
        //             future_att_consensus_instances_already_decided := toCoVNodeState(this).future_att_consensus_instances_already_decided
        //         )
        //         invariant toCoVNodeStateAndOuputs(this).outputs == getEmptyOuputs();
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

        //     assert block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toCoVNodeState(this)), block) == toCoVNodeStateAndOuputs(this);
        // }        

        // method listen_for_new_imported_blocks...
        // // ensures block.body.state_root in bn.state_roots_of_imported_blocks ==> f_listen_for_new_imported_blocks(old(toCoVNodeState(this)), block) == toCoVNodeStateAndOuputs(this);
        // {
        //     ...;

        //     while...
        //         invariant 0 <= i <= |block.body.attestations|
        //         // invariant 
        //         // var new_att := future_att_consensus_instances_already_decided - old(this.future_att_consensus_instances_already_decided); 
        //         // var process := old(toCoVNodeState(this));
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
        //         var process := old(toCoVNodeState(this));
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
        //             var process := old(toCoVNodeState(this));
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
        ensures f_resend_attestation_share(old(toCoVNodeState(this))) == toCoVNodeStateAndOuputs(this)
        {
            ...;
            assert  f_resend_attestation_share(old(toCoVNodeState(this))) == toCoVNodeStateAndOuputs(this);
        }
    }
}


// module A {
//   method ToImplement(x: int) returns (r: int)
//     ensures r > x

//   method ToStrengthen(x: int) returns (r: int)

//   method ToDeterminize(x: int) returns (r: int)
//     ensures r >= x
//   {
//     var y :| y >= x;
//     return y;
//   }

//   method ToSuperimpose(x: int) returns (r: int)
//   {
//     var y: int := x;
//     if y < 0 {
//       return -y;
//     } else {
//       return y;
//     }
//   }

// }

// module B refines A {
//   method ToImplement(x: int) returns (r: int)
//   {
//     return x + 2;
//   }

//   method ToStrengthen...
//     ensures r == x*2
//   {
//     return x*2;
//   }

//   method ToDeterminize(x: int) returns (r: int)
//   {
//     return x;
//   }

//   method ToSuperimpose(x: int) returns (r: int)
//   ensures r >= 0
//   {
//     ...;
//     if y < 0 {
//       print "inverting";
//       return -1;
//     } else {
//       print "not modifying";
//       return -1;
//     }
//   }
// }