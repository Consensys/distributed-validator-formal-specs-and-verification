include "../common/commons.dfy"
include "./dvc_externs.dfy"

abstract module Att_DVC_Implementation
{
    import opened Types
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened DVC_Externs : DVC_Externs

    export PublicInterface
        reveals Att_DVC        
        provides
                Att_DVC.process_event,
                Att_DVC.getRepr,
                Att_DVC.ValidConstructorRepr,
                Att_DVC.ValidRepr
        provides Types, DVC_Externs

    class Att_DVC {
        var current_attestation_duty: Optional<AttestationDuty>;
        var latest_attestation_duty: Optional<AttestationDuty>;
        var rcvd_attestation_shares: map<Slot,map<(AttestationData, seq<bool>), set<AttestationShare>>>;
        var attestation_shares_to_broadcast: map<Slot, AttestationShare>
        var construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>;
        var peers: set<BLSPubkey>;
        var dv_pubkey: BLSPubkey;
        var future_att_consensus_instances_already_decided: map<Slot, AttestationData>

        const slashing_db: SlashingDB<SlashingDBAttestation>;
        const att_consensus: Consensus<AttestationData, SlashingDBAttestation>;
        const network : Network
        const bn: BeaconNode<Attestation>;
        const rs: RemoteSigner;

        constructor(
            pubkey: BLSPubkey, 
            dv_pubkey: BLSPubkey,
            att_consensus: Consensus<AttestationData, SlashingDBAttestation>, 
            peers: set<BLSPubkey>,
            network: Network,
            bn: BeaconNode<Attestation>,
            rs: RemoteSigner,
            initial_slashing_db: SlashingDB<SlashingDBAttestation>,
            construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>
        )
        // The following indicates that `att_consensus` must not have any active consensus instance running.
        // This may need to be strengthened to require that `att_consensus` has never started any consensus instance.
        requires att_consensus.consensus_instances_started == map[]
        requires ValidConstructorRepr(att_consensus, network, bn, rs, initial_slashing_db)
        {
            this.current_attestation_duty := None;
            this.latest_attestation_duty := None;
            this.slashing_db := initial_slashing_db;
            this.attestation_shares_to_broadcast := map[];
            this.rcvd_attestation_shares := map[];
            this.future_att_consensus_instances_already_decided := map[];
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
            event: AttestationEvent
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            match event {
                case ServeAttestationDuty(attestation_duty) => 
                    :- serve_attestation_duty(attestation_duty);
                case AttConsensusDecided(id, decided_attestation_data) => 
                    :- att_consensus_decided(id,  decided_attestation_data);
                case ReceivedAttestationShare(attestation_share) => 
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
            { 
                // Error: terminate_current_attestation_duty();
                if current_attestation_duty.isPresent()
                {
                    current_attestation_duty := None;           
                }
                else
                {
                }
                :- check_for_next_duty(attestation_duty);
            }

            return Success;
        }

        // Using this method raises errors
        // method terminate_current_attestation_duty() 
        // // returns (s: Status)
        // requires ValidRepr()
        // modifies getRepr()
        // ensures  ValidRepr()
        // {
        //     if current_attestation_duty.isPresent()
        //     {
        //         current_attestation_duty := None;           
        //     }
        //     else
        //     {
        //     }

        //     // return Success;
        // }  

        method check_for_next_duty(
            attestation_duty: AttestationDuty
        ) returns (s: Status) // TODO T/O
        requires ValidRepr()
        modifies getRepr()
        {
            if attestation_duty.slot in future_att_consensus_instances_already_decided.Keys
            {
                update_attestation_slashing_db(future_att_consensus_instances_already_decided[attestation_duty.slot]);
                future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided - {attestation_duty.slot};                    
            }
            else if !current_attestation_duty.isPresent()
            {
                :- start_next_duty(attestation_duty);
            }

            return Success;
        }

        method start_next_duty(attestation_duty: AttestationDuty) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            current_attestation_duty := Some(attestation_duty);
            latest_attestation_duty := Some(attestation_duty);
            var validityCheck := new AttestationConsensusValidityCheck(this.dv_pubkey, this.slashing_db, attestation_duty);
            { :- att_consensus.start(attestation_duty.slot, validityCheck);}
            return Success;
        }        

        method update_attestation_slashing_db(attestation_data: AttestationData)
        requires ValidRepr()
        modifies slashing_db.Repr
        ensures fresh(slashing_db.Repr - old(slashing_db.Repr))
        ensures  ValidRepr()
        {
            var slashing_db_attestation := SlashingDBAttestation(
                                                source_epoch := attestation_data.source.epoch,
                                                target_epoch := attestation_data.target.epoch,
                                                signing_root := Some(hash_tree_root(attestation_data)));
            slashing_db.add_record(slashing_db_attestation, dv_pubkey);
        }

        method att_consensus_decided(
            id: Slot,
            decided_attestation_data: AttestationData
        ) returns (r: Status)
        requires ValidRepr()
        modifies getRepr()
        {
              
            if  && current_attestation_duty.isPresent()
                && current_attestation_duty.safe_get().slot == id
            {
                var local_current_attestation_duty := current_attestation_duty.safe_get();    
                update_attestation_slashing_db(decided_attestation_data);
    
                var fork_version := bn.get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
                var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
                var attestation_signature_share := rs.sign_attestation(decided_attestation_data, fork_version, attestation_signing_root);
                var attestation_with_signature_share := 
                        AttestationShare(
                            aggregation_bits := f_get_aggregation_bits(local_current_attestation_duty.validator_index),
                            data := decided_attestation_data, 
                            signature :=attestation_signature_share
                        ); 

                attestation_shares_to_broadcast := attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share];
                network.send_att_share(attestation_with_signature_share, peers);  
                current_attestation_duty := None;
            }

            return Success;         
        }

        function method f_get_aggregation_bits(
            index: nat
        ): seq<bool>
        {
            seq(index, i => if i + 1 == index then true else false)
        }        

        method listen_for_attestation_shares(
            attestation_share: AttestationShare
        )
        requires ValidRepr()
        modifies getRepr()
        {
            var activate_att_consensus_intances := att_consensus.get_active_instances();

            if 
                || (activate_att_consensus_intances == {} && !latest_attestation_duty.isPresent())
                || (activate_att_consensus_intances != {} && minInSet(activate_att_consensus_intances) <= attestation_share.data.slot)
                // || (activate_att_consensus_intances == {} && current_attestation_duty.isPresent() && current_attestation_duty.safe_get().slot <= attestation_share.data.slot)                
                || (activate_att_consensus_intances == {} && !current_attestation_duty.isPresent() && latest_attestation_duty.isPresent() && latest_attestation_duty.safe_get().slot < attestation_share.data.slot)
            {
                // TODO: The check above is not consistent with the clean-up operation done in
                // listen_for_new_imported_blocks. Here, any share for future slot is accepted, whereas
                // listen_for_new_imported_blocks cleans up the received shares for any already-decided slot. This
                // inconsistency should be fixed up by either accepting here only shares with slot higher than the
                // maximum already-decided slot or changing the clean-up code in listen_for_new_imported_blocks to clean
                // up only slot lower thant the slot of the current/latest duty 
                var k := (attestation_share.data, attestation_share.aggregation_bits);
                var attestation_shares_db_at_slot := get_or_default(rcvd_attestation_shares, attestation_share.data.slot, map[]);
                rcvd_attestation_shares := 
                    rcvd_attestation_shares[
                        attestation_share.data.slot := 
                            attestation_shares_db_at_slot[
                                        k := 
                                            get_or_default(attestation_shares_db_at_slot, k, {}) + 
                                            {attestation_share}
                                        ]
                            ];
                            
                if construct_signed_attestation_signature(rcvd_attestation_shares[attestation_share.data.slot][k]).isPresent()
                {
                    var aggregated_attestation := 
                        f_construct_aggregated_attestation_for_new_attestation_share(
                            attestation_share,
                            k, 
                            construct_signed_attestation_signature,
                            rcvd_attestation_shares
                        );

                    bn.submit_data(aggregated_attestation); 
                } 
            } 
        }

        

        method listen_for_new_imported_blocks(
            block: BeaconBlock
        ) returns (s: Status)
        requires ValidRepr()
        modifies getRepr()
        {
            var valIndex :- bn.get_validator_index(block.body.state_root, dv_pubkey);
            var i := 0;

            var att_consensus_instances_already_decided := this.future_att_consensus_instances_already_decided;



            while i < |block.body.attestations|
                invariant ValidRepr() && fresh(bn.Repr - old(bn.Repr)) && unchanged(rs) && unchanged(network) && unchanged(att_consensus) && unchanged(this) && unchanged(slashing_db)
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
                && ( || !latest_attestation_duty.isPresent()
                     || ( && latest_attestation_duty.isPresent() 
                          && latest_attestation_duty.safe_get().slot < a.data.slot ) )
                {
                    att_consensus_instances_already_decided := att_consensus_instances_already_decided[a.data.slot := a.data];
                }

                i := i + 1;
            }

            att_consensus.stop_multiple(att_consensus_instances_already_decided.Keys);
            // TODO: The clean-up below is not consistent with the check done in listen_for_attestation_shares. See
            // comment in listen_for_attestation_shares for an explanation.         
            attestation_shares_to_broadcast := attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys;
            rcvd_attestation_shares := rcvd_attestation_shares - att_consensus_instances_already_decided.Keys;

            // This block refers to f_..._helper_2
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

            if current_attestation_duty.isPresent() && current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided
            {
                update_attestation_slashing_db(att_consensus_instances_already_decided[current_attestation_duty.safe_get().slot]);
                current_attestation_duty := None;
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
            att_consensus: Consensus<AttestationData, SlashingDBAttestation>, 
            network: Network,
            bn: BeaconNode<Attestation>,
            rs: RemoteSigner,
            slashing_db: SlashingDB<SlashingDBAttestation>            
        )
        reads *
        {
            && att_consensus.consensus_instances_started.Values 
            !! bn.Repr !! network.Repr !! att_consensus.Repr 
            !! rs.Repr !! slashing_db.Repr
            && bn.Valid()
            && rs.Valid()
            && network.Valid()
            && att_consensus.Valid()    
            && slashing_db.Valid()                            
        }   

        function getChildrenRepr(): set<object?>
        reads *
        {
            this.att_consensus.consensus_instances_started.Values 
            + this.bn.Repr + this.network.Repr + this.att_consensus.Repr + this.rs.Repr
            + this.slashing_db.Repr
        }        

        function getRepr(): set<object?>
        reads *
        {
            getChildrenRepr() + {this}
        }

        predicate ValidRepr()
        reads *
        {
            && ValidConstructorRepr(this.att_consensus, this.network, this.bn, this.rs, this.slashing_db)
            && this !in getChildrenRepr()                                
        }              
    }  

    class AttestationConsensusValidityCheck extends ConsensusValidityCheck<AttestationData, SlashingDBAttestation>
    {
        const dv_pubkey: BLSPubkey
        const attestation_duty: AttestationDuty

        constructor(
            dv_pubkey: BLSPubkey,
            slashing_db: SlashingDB<SlashingDBAttestation>,
            attestation_duty: AttestationDuty
        )
        requires slashing_db.Valid()
        ensures this.dv_pubkey == dv_pubkey
        ensures this.attestation_duty == attestation_duty
        ensures this.slashing_db == slashing_db
        ensures Valid()
        {
            this.dv_pubkey := dv_pubkey;
            this.attestation_duty := attestation_duty;
            this.slashing_db := slashing_db;
            Repr := {this} + {slashing_db} + slashing_db.Repr;
        }

        method is_valid(data: AttestationData) returns (valid: bool)
        requires Valid()
        modifies Repr
        ensures Valid()
        ensures fresh(Repr - old(Repr))
        {
            assert Valid();
            assert slashing_db.Valid();
            var attestations := slashing_db.get_records(dv_pubkey);
            Repr := Repr + slashing_db.Repr;

            return ci_decision_att_signature_is_signed_with_pubkey_data(attestations, data, this.attestation_duty);             
        }
    }      
}


