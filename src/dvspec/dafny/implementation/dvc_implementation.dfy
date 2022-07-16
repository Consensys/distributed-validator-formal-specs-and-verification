include "../commons.dfy"

abstract module DVCNode_Implementation
{
    import opened Types
    import opened CommonFunctions
    import opened DVCNode_Externs : DVCNode_Externs

    export PublicInterface
        reveals DVCNode        
        provides
                DVCNode.process_event,
                DVCNode.getRepr,
                DVCNode.ValidConstructorRepr,
                DVCNode.ValidRepr
        provides Types, DVCNode_Externs

    class DVCNode {

        var current_attesation_duty: Optional<AttestationDuty>;
        var latest_attestation_duty: Optional<AttestationDuty>;
        var attestation_duties_queue: seq<AttestationDuty>;
        var attestation_slashing_db: AttestationSlashingDB;
        var attestation_shares_db: map<Slot,map<(AttestationData, seq<bool>), set<AttestationShare>>>;
        var attestation_shares_to_broadcast: map<Slot, AttestationShare>
        var construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>;
        var peers: set<BLSPubkey>;
        var dv_pubkey: BLSPubkey;
        var future_att_consensus_instances_already_decided: map<Slot, AttestationData>

        const att_consensus: Consensus<AttestationData>;
        const network : Network
        const bn: BeaconNode;
        const rs: RemoteSigner;

        constructor(
            pubkey: BLSPubkey, 
            dv_pubkey: BLSPubkey,
            att_consensus: Consensus<AttestationData>, 
            peers: set<BLSPubkey>,
            network: Network,
            bn: BeaconNode,
            rs: RemoteSigner,
            initial_attestation_slashing_db: AttestationSlashingDB,
            construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>
        )
        // The following indicates that `att_consensus` must not have any active consensus instance running.
        // This may need to be strengthened to require that `att_consensus` has never started any consensus instance.
        requires att_consensus.consensus_instances_started == map[]
        requires ValidConstructorRepr(att_consensus, network, bn, rs)
        {
            current_attesation_duty := None;
            latest_attestation_duty := None;
            attestation_duties_queue := [];
            attestation_slashing_db := initial_attestation_slashing_db;
            attestation_shares_to_broadcast := map[];
            attestation_shares_db := map[];
            future_att_consensus_instances_already_decided := map[];

            this.att_consensus := att_consensus;
            this.peers := peers;
            this.network := network;
            this.rs := rs;
            this.bn := bn;
            this.construct_signed_attestation_signature := construct_signed_attestation_signature;
            this.dv_pubkey := dv_pubkey;        
        }
    
        /*=================================================================================
         * Public methods
         * ===============================================================================*/

        method process_event(
            event: Event
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            match event {
                case ServeAttstationDuty(attestation_duty) => 
                    :- serve_attestation_duty(attestation_duty);
                case AttConsensusDecided(id, decided_attestation_data) => 
                    :- att_consensus_decided(id,  decided_attestation_data);
                case ReceviedAttesttionShare(attestation_share) => 
                    listen_for_attestation_shares(attestation_share);
                case ImportedNewBlock(block) => 
                    :- listen_for_new_imported_blocks(block);
                case ResendAttestationShares => 
                    resend_attestation_share();
                case NoEvent =>
                    
            }

            {return Success;}
        }   
        
        /*=================================================================================
         * Private methods
         * ===============================================================================*/        

        method serve_attestation_duty(
            attestation_duty: AttestationDuty
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            attestation_duties_queue := attestation_duties_queue + [attestation_duty];
            {
                :- check_for_next_queued_duty();
            }

            return Success;
        }

        method check_for_next_queued_duty() returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        decreases attestation_duties_queue
        {
            if attestation_duties_queue != []
            {
                if attestation_duties_queue[0].slot in future_att_consensus_instances_already_decided.Keys
                {
                    var queue_head := attestation_duties_queue[0];
                    attestation_duties_queue := attestation_duties_queue[1..];
                    update_attestation_slashing_db(future_att_consensus_instances_already_decided[queue_head.slot]);
                    { :- check_for_next_queued_duty();}
                }
                else if !current_attesation_duty.isPresent()
                {
                    var queue_head := attestation_duties_queue[0];
                    attestation_duties_queue := attestation_duties_queue[1..];

                    :- start_next_duty(queue_head);
                }
            }

            return Success;
        }

        method start_next_duty(attestation_duty: AttestationDuty) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            current_attesation_duty := Some(attestation_duty);
            latest_attestation_duty := Some(attestation_duty);
            var validityCheck := new AttestationConsensusValidityCheck(this, attestation_duty);
            { :- att_consensus.start(attestation_duty.slot, validityCheck);}
            return Success;
        }        

        method update_attestation_slashing_db(attestation_data: AttestationData)
        modifies `attestation_slashing_db
        {
            var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := Some(hash_tree_root(attestation_data)));
            attestation_slashing_db := attestation_slashing_db + {slashing_db_attestation};
        }

        method att_consensus_decided(
            id: Slot,
            decided_attestation_data: AttestationData
        ) returns (r: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            var local_current_attestation_duty :- current_attesation_duty.get();            
            update_attestation_slashing_db(decided_attestation_data);
 
            var fork_version := bn.get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs.sign_attestation(decided_attestation_data, fork_version, attestation_signing_root);
            var attestation_with_signature_share := AttestationShare(
                aggregation_bits := get_aggregation_bits(local_current_attestation_duty.validator_index),
                data := decided_attestation_data, 
                signature :=attestation_signature_share
            ); 

            attestation_shares_to_broadcast := attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share];
            network.send_att_share(attestation_with_signature_share, peers);  
            current_attesation_duty := None;
            
            { :- check_for_next_queued_duty(); }

            return Success;         
        }

        function method get_aggregation_bits(
            index: nat
        ): (s: seq<bool>)
        ensures |s| == index
        ensures forall i | 0 <= i < |s| :: if i == index - 1 then s[i] else !s[i]
        {
            seq(index, i => if i + 1 == index then true else false)
        }        

        method listen_for_attestation_shares(
            attestation_share: AttestationShare
        )
        requires ValidRepr()
        modifies getRepr()
        {
            // TODO: Decide 
            // 1. whether to add att shares to db only if already served attestation duty
            // 2. when to wipe out the db
            var activate_att_consensus_intances := att_consensus.get_active_instances();

            if 
                || (activate_att_consensus_intances == {} && !latest_attestation_duty.isPresent())
                || (activate_att_consensus_intances != {} && minSet(activate_att_consensus_intances) <= attestation_share.data.slot)
                || (activate_att_consensus_intances == {} && current_attesation_duty.isPresent() && current_attesation_duty.safe_get().slot <= attestation_share.data.slot)                
                || (activate_att_consensus_intances == {} && !current_attesation_duty.isPresent() && latest_attestation_duty.isPresent() && latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
            {
                var k := (attestation_share.data, attestation_share.aggregation_bits);
                var attestation_shares_db_at_slot := getOrDefault(attestation_shares_db, attestation_share.data.slot, map[]);
                attestation_shares_db := 
                    attestation_shares_db[
                        attestation_share.data.slot := 
                            attestation_shares_db_at_slot[
                                        k := 
                                            getOrDefault(attestation_shares_db_at_slot, k, {}) + 
                                            {attestation_share}
                                        ]
                            ];
                            
                if construct_signed_attestation_signature(attestation_shares_db[attestation_share.data.slot][k]).isPresent()
                {
                    var aggregated_attestation := 
                            Attestation(
                                aggregation_bits := attestation_share.aggregation_bits,
                                data := attestation_share.data,
                                signature := construct_signed_attestation_signature(attestation_shares_db[attestation_share.data.slot][k]).safe_get()
                            );
                    bn.submit_attestation(aggregated_attestation); 
                } 
            } 
        }

        method listen_for_new_imported_blocks(
            block: BeaconBlock
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            var r := bn.Repr;
            var valIndex :- bn.get_validator_index(block.body.state_root, dv_pubkey);
            var i := 0;

            var att_consensus_instances_already_decided := future_att_consensus_instances_already_decided;

            while i < |block.body.attestations|
            invariant ValidRepr() && fresh(bn.Repr - old(bn.Repr)) 
            && unchanged(rs)
            && unchanged(network)
            && unchanged(att_consensus)
            && unchanged(this)
            {
                var a := block.body.attestations[i];

                var committee:- bn.get_epoch_committees(block.body.state_root, a.data.index);
                
                if
                && a in block.body.attestations
                && valIndex.Some?
                && valIndex.v in committee
                && var i:nat :| i < |committee| && committee[i] == valIndex.v;
                && i < |a.aggregation_bits|
                && a.aggregation_bits[i]
                {
                    att_consensus_instances_already_decided := att_consensus_instances_already_decided[a.data.slot := a.data];
                }

                i := i + 1;
            }

            att_consensus.stop_multiple(att_consensus_instances_already_decided.Keys);
            attestation_shares_to_broadcast := attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys;
            attestation_shares_db := attestation_shares_db - att_consensus_instances_already_decided.Keys;

            if latest_attestation_duty.isPresent()
            {
                var old_instances := 
                        set i | 
                            && i in att_consensus_instances_already_decided.Keys
                            && i <= latest_attestation_duty.safe_get().slot
                        ;
                future_att_consensus_instances_already_decided := att_consensus_instances_already_decided - old_instances;
            }
            else
            {
                future_att_consensus_instances_already_decided := att_consensus_instances_already_decided;
            }            

            if current_attesation_duty.isPresent() && current_attesation_duty.safe_get().slot in att_consensus_instances_already_decided
            {
                // update_attestation_slashing_db(att_consensus_instances_already_decided[current_attesation_duty.safe_get().slot]);
                current_attesation_duty := None;
                { :- check_for_next_queued_duty();}
            }

            return Success;                              
        }

        method resend_attestation_share()
        requires ValidRepr()
        modifies getRepr()
        {
            network.send_att_shares(attestation_shares_to_broadcast.Values, peers);
        }     

        static predicate ValidConstructorRepr(
            att_consensus: Consensus<AttestationData>, 
            network: Network,
            bn: BeaconNode,
            rs: RemoteSigner            
        )
        reads *
        {
            && att_consensus.consensus_instances_started.Values 
            !! bn.Repr !! network.Repr !! att_consensus.Repr !! rs.Repr
            && bn.Valid()
            && rs.Valid()
            && network.Valid()
            && att_consensus.Valid()                                
        }   

        function getChildrenRepr(): set<object?>
        reads *
        {
            this.att_consensus.consensus_instances_started.Values 
            + this.bn.Repr + this.network.Repr + this.att_consensus.Repr + this.rs.Repr
        }        

        function getRepr(): set<object?>
        reads *
        {
            getChildrenRepr() + {this}
        }

        predicate ValidRepr()
        reads *
        {
            && ValidConstructorRepr(this.att_consensus, this.network, this.bn, this.rs)
            && this
            !in getChildrenRepr()                                
        }              
    }  

    class AttestationConsensusValidityCheck extends ConsensusValidityCheck<AttestationData>
    {
        const dvcNode: DVCNode
        const attestation_duty: AttestationDuty

        constructor(
            dvcNode: DVCNode,
            attestation_duty: AttestationDuty
        )
        ensures this.dvcNode == dvcNode
        ensures this.attestation_duty == attestation_duty
        {
            this.dvcNode := dvcNode;
            this.attestation_duty := attestation_duty;
        }

        predicate is_valid(data: AttestationData)
        reads *
        {
            consensus_is_valid_attestation_data(dvcNode.attestation_slashing_db, data, this.attestation_duty)             
        }
    }      
}

module DVCNode_Externs
{
    import opened Types
    import opened CommonFunctions

    trait {:autocontracts} Consensus<T(!new, ==)>
    {
        ghost var consensus_instances_started: map<Slot, ConsensusValidityCheck<T>>

        method start(
            id: Slot,
            validityPredicate: ConsensusValidityCheck<T>
        ) returns (s: Status)
        // requires validityPredicate as object != this
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

    }

    trait {:autocontracts} BeaconNode
    {
        ghost var state_roots_of_imported_blocks: set<Root>;
        ghost var attestations_submitted: seq<Attestation>; 

        method get_fork_version(s: Slot) returns (v: Version)
        ensures unchanged(`state_roots_of_imported_blocks)
        ensures unchanged(`attestations_submitted)

        method submit_attestation(attestation: Attestation)
        ensures attestations_submitted == old(attestations_submitted) + [attestation]
        ensures unchanged(`state_roots_of_imported_blocks)

        // https://ethereum.github.io/beacon-APIs/?urls.primaryName=v1#/Beacon/getEpochCommittees
        method get_epoch_committees(
            state_id: Root,
            index: CommitteeIndex
        ) returns (s: Status, sv: seq<ValidatorIndex>)
        ensures unchanged(`state_roots_of_imported_blocks)
        ensures unchanged(`attestations_submitted)        
        ensures state_id in state_roots_of_imported_blocks <==> s.Success?
        ensures uniqueSeq(sv)  

        // https://ethereum.github.io/beacon-APIs/#/Beacon/getStateValidator
        method get_validator_index(
            state_id: Root,
            validator_id: BLSPubkey
        ) returns (s: Status, vi: Optional<ValidatorIndex>)
        ensures unchanged(`state_roots_of_imported_blocks)
        ensures unchanged(`attestations_submitted)        
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

    }
}

