type ValidatorIndex = nat
type Epoch(==)
type Slot(==)
type CommitteeIndex
// type Attestation 
type BLSSignature(==)
type BLSPubkey(==)
type Bytes32
// type SignedBeaconBlock
type Root 
type SyncCommitteeSignature
datatype Checkpoint = Checkpoint(
    epoch: Epoch,
    root: Root
)
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
type BeaconBlock(==)
type SyncCommitteeDuty   
type Version


datatype Attestation = Attestation(
    aggregation_bits: seq<bool>,
    data: AttestationData,
    signature: BLSSignature
)

datatype AttestationShare = AttestationShare(
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

datatype AttestationSlashingDB = AttestationSlashingDB
// class AttestationSlashingDB
// {

// }

datatype BlockSlashingDB = BlockSlashingDB

datatype Optional<T> = Some(v: T) | None
{
    predicate isPresent()
    {
        this.Some?
    }

    function get(): T 
    requires isPresent()
    {
        this.v
    }
}

function method consensus_on_attestation(slashing_db: AttestationSlashingDB, attestation_duty: AttestationDuty): AttestationData

function method compute_start_slot_at_epoch(epoch: Epoch): Slot

function method bn_get_fork_version(slot: Slot): Version

function method compute_attestation_signing_root(attestation_data: AttestationData): Root

function method rs_sign_attestation(attestation_data: AttestationData, fork_version: Version, signing_root: Root): BLSSignature

method update_attestation_slashing_db(slashing_db: AttestationSlashingDB, attestation_data: AttestationData, attestation_duty_pubkey: BLSPubkey)

function f_update_attestation_slashing_db(slashing_db: AttestationSlashingDB, attestation_data: AttestationData, attestation_duty_pubkey: BLSPubkey): AttestationSlashingDB


method broadcast_attestation_signature_share(attstationg: AttestationShare)


method serve_attestation_duty(slashing_db: AttestationSlashingDB, attestation_duty: AttestationDuty)
{
    // TODO: Is lock on consensus the best way to do this? Does lock on slashing DB work?
    // Obtain lock on consensus_on_attestation here.
    // Only a single consensus_on_attestation instance should be
    // running at any given time
    var attestation_data := consensus_on_attestation(slashing_db, attestation_duty);
    // assert consensus_is_valid_attestation_data(slashing_db, attestation_data, attestation_duty)
    // Release lock on consensus_on_attestation here.
    // Add attestation to slashing DB
    update_attestation_slashing_db(slashing_db, attestation_data, attestation_duty.pubkey);
    // Sign attestation using RS
    // TODO: Reuse fork version from here in compute_domain
    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(attestation_data.target.epoch));
    var attestation_signing_root := compute_attestation_signing_root(attestation_data);
    var attestation_signature_share := rs_sign_attestation(attestation_data, fork_version, attestation_signing_root);
    // TODO: What is attestation_signature_share.aggregation_bits?
    var attestation_with_signature_share := AttestationShare(data :=attestation_data, signature :=attestation_signature_share);
    // TODO: Should we just gossip & recombine the signature shares without attestation data?
    broadcast_attestation_signature_share(attestation_with_signature_share);
}



datatype CONSENSUS_TYPE = ATTESTATION_CONSENSUS | BLOCK_CONSENSUS
// type ConsensusID = (CONSENSUS_TYPE, Slot)

datatype ProcessOutput<!T1, T2> =
|   NewProcessStateAndStartConsensusInstance(
        new_process_state: ServeAttesationProcess,
        start_consensus_with_instance_id: Slot
        // ,initial_value: T1
        // ,validity_function: T1 -> bool
    )
// |   StopConsensus(
//         start_consensus_with_instance_id: (CONSENSUS_TYPE, Slot)
//     )
|   SignatureShareToBroadcastAndNewProcessState(signature_share: T2, new_process_state: ServeAttesationProcess)
|   NewProcessState(new_process_state: ServeAttesationProcess)
|   NewProcessStateAndAggregatedAttestation(
        aggregated_attestations: set<Attestation>,
        new_process_state: ServeAttesationProcess
)

type COValidatorID(==)

datatype ServeAttesationProcess = ServeAttesationProcess(
    attestation_duty: AttestationDuty,
    construct_signed_attestation_signature: (AttestationData, set<BLSSignature>) -> Optional<BLSSignature>,
    signature_shares_db: AttestationSignatureShareDB,
    // co_validators: map<BLSPubkey, COValidatorID>
    slashing_db: AttestationSlashingDB
)

predicate verify_bls_siganture<T>(
    data: T,
    signature: BLSSignature,
    pubkey: BLSPubkey
)

datatype ServeAttestationProcessInputEvent = 
| StartProcess(slashing_db: AttestationSlashingDB)
| ConsenusHasDecided(decided_value: AttestationData, slashing_db: AttestationSlashingDB)

function f_serve_attestation_duty(process: ServeAttesationProcess, input_event: ServeAttestationProcessInputEvent): ProcessOutput<AttestationData, AttestationShare>
// {

// }

predicate is_slashable_attestation_data(slashing_db: AttestationSlashingDB, attestation_data: AttestationData, pubkey: BLSPubkey)

predicate consensus_is_valid_attestation_data(slashing_db: AttestationSlashingDB, attestation_data: AttestationData, attestation_duty: AttestationDuty) 
{
    && attestation_data.slot == attestation_duty.slot
    && attestation_data.index == attestation_duty.committee_index
    && !is_slashable_attestation_data(slashing_db, attestation_data, attestation_duty.pubkey)    
}

function f_serve_attestation_duty_start(
    process: ServeAttesationProcess,
    attestation_duty: AttestationDuty
    // ,slashing_db: AttestationSlashingDB
): ProcessOutput<AttestationData, AttestationShare>
{
    NewProcessStateAndStartConsensusInstance(
        start_consensus_with_instance_id := attestation_duty.slot,
        new_process_state := process.(attestation_duty := attestation_duty)
        // ,validity_function := (attestation_data: AttestationData) => 
        //     && attestation_data.slot == attestation_duty.slot
        //     && attestation_data.index == attestation_duty.committee_index
        //     && !is_slashable_attestation_data(slashing_db, attestation_data, attestation_duty.pubkey)
        
    )
}

predicate no_slashing_conditions_in_the_slashing_db(slashing_db: AttestationSlashingDB)

function f_serve_attestation_duty_consensus_finished(
    process: ServeAttesationProcess
    , decided_attestation_data: AttestationData
    // , slashing_db: AttestationSlashingDB
): ProcessOutput<AttestationData, AttestationShare>
{
    var new_slashing_db := f_update_attestation_slashing_db(process.slashing_db, decided_attestation_data, process.attestation_duty.pubkey);
    // Sign attestation using RS
    // TODO: Reuse fork version from here in compute_domain
    var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
    var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data);
    var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root);
    // TODO: What is attestation_signature_share.aggregation_bits?
    var attestation_with_signature_share := AttestationShare(data := decided_attestation_data, signature :=attestation_signature_share);
    // TODO: Should we just gossip & recombine the signature shares without attestation data?
    // broadcast_attestation_signature_share(attestation_with_signature_share);
    SignatureShareToBroadcastAndNewProcessState(
        signature_share:= attestation_with_signature_share,
        new_process_state := process.(slashing_db := new_slashing_db)
    )
}

type AttestationSignatureShareDB = map<AttestationData, set<BLSSignature>>

// function mapPutIfAbsent<T1,T2>(M:map<T1,T2>, key:T1, value:T2): map<T1,T2>
//     {
//         if key !in M.Keys then
//             M[
//                 key := value
//             ]
//         else
//             M
//     }

function getOrDefault<T1,T2>(M:map<T1,T2>, key:T1, default:T2): T2
    {
        if key in M.Keys then
            M[key]
        else
            default
    }   

function get_aggregation_bits(
    process: ServeAttesationProcess
): seq<bool>

datatype AggregatedAttestationAndAttestationSignatureShareDB = AggregatedAttestationAndAttestationSignatureShareDB(
    aggregated_attestations: set<Attestation>,
    new_attestation_signature_share_db: AttestationSignatureShareDB
)

// predicate verify_attestation_share_sender(
//     attestation_share: AttestationShare,
//     sender_pubkey: BLSPubkey
// )
// // returs true iff the signature in attestation share is a valid signature for a node with pubkey `sender_pubkey`.

// function get_attestation_share_sender(
//     attestation_share: AttestationShare,
//     co_validators: map<BLSPubkey, COValidatorID>
// ): Optional<COValidatorID>

function construct_signed_attestation_signature(
    attestation_data_to_signatures_map: map<AttestationData, set<BLSSignature>>
): set<(AttestationData, BLSSignature)>

function f_listen_for_attestation_signature_shares(
    process: ServeAttesationProcess, 
    // signature_shares_db: AttestationSignatureShareDB, 
    attestation_share: AttestationShare): ProcessOutput<AttestationData, AttestationShare>
{

    var sets_of_signatures_for_attestation_data := getOrDefault(process.signature_shares_db, attestation_share.data, {});

    var new_signature_shares_db := process.signature_shares_db[attestation_share.data := 
        sets_of_signatures_for_attestation_data + {attestation_share.signature}];

    var aggregated_attestations := 
        set k | 
                && k in new_signature_shares_db.Keys 
                && process.construct_signed_attestation_signature(k, new_signature_shares_db[k]).isPresent()
            ::
                Attestation(
                    aggregation_bits := get_aggregation_bits(process),
                    data := k,
                    signature := process.construct_signed_attestation_signature(k, new_signature_shares_db[k]).get()
                );
                

    NewProcessStateAndAggregatedAttestation(
        aggregated_attestations,
        new_process_state := process.(signature_shares_db := new_signature_shares_db)
    )
}

type NodeID(==)
datatype NSState = NSState

/*
datatype Adversary = Adversary(
    num_nodes: nat
)

datatype DSVState = DSVState(
    honest_node_states: seq<NSState>,
    adversary: Adversary
)

predicate DSVInit(s: DSVState, num_honest_nodes: nat, num_byz_nodes: nat, attestation_duty: AttestationDuty, d_pubkey: BLSPubkey )
{
    && |s.honest_node_states| == num_honest_nodes
    && s.adversary.num_nodes == num_byz_nodes
}
*/


datatype Adversary = Adversary(
    nodes: set<BLSPubkey>
)

// datatype DVSAttestationConsensusDataPerNode = DVSAttestationConsensusDataPerNode
// (
//     slashing_dbs: set<AttestationSlashingDB>,
//     running:
// )

datatype DVSAttestationConsensusData = DVSAttestationConsensusData(
    decided_value: Optional<AttestationData>,
    honest_nodes_running: set<BLSPubkey>
)

type imaptotal<!T1(!new), T2> = x: imap<T1,T2> | forall e: T1 :: e in x.Keys witness *

datatype DSVState = DSVState(
    all_nodes: set<BLSPubkey>,
    honest_nodes_states: map<BLSPubkey, ServeAttesationProcess>,
    adversary: Adversary,
    dv_pubkey: BLSPubkey,
    attestations_shares_sent: set<AttestationShare>,
    consensus_on_attestation_data: imaptotal<Slot, DVSAttestationConsensusData>,
    slashing_dbs_used_for_validating_attestations: imaptotal<Slot, set<AttestationSlashingDB>>,
    aggregated_attestations_sent: set<Attestation>,
    attestation_duties_served: map<AttestationDuty, set<BLSPubkey>>,
    construct_signed_attestation_signature: (AttestationData, set<BLSSignature>) -> Optional<BLSSignature>
)

function f(n:nat): nat
requires n > 0 
{
    (n-1)/3
}

function quorum(n:nat):nat
// returns ceil(2n/3)

predicate DSVInit(
    s: DSVState,
    initial_slashing_db: AttestationSlashingDB
)
{
    && s.honest_nodes_states.Keys !! s.adversary.nodes !! {s.dv_pubkey}
    && s.all_nodes == s.honest_nodes_states.Keys + s.adversary.nodes
    && s.honest_nodes_states != map[]
    && |s.adversary.nodes| <= f(|s.all_nodes|)
    && (
        forall 
            data: AttestationData, 
            sig_shares: set<BLSSignature> 
            ::
            (
                exists verifiable_sig_shares: set<BLSSignature> ::
                    && verifiable_sig_shares <= sig_shares
                    && quorum(|verifiable_sig_shares|) >= |s.all_nodes|
                    && (forall sig_share |
                        sig_share in verifiable_sig_shares ::
                            exists signer :: 
                                && signer in s.all_nodes
                                && verify_bls_siganture(data, sig_share, signer)
                    )
            )
            <==>
                s.construct_signed_attestation_signature(data, sig_shares).isPresent()
    )    
    &&
        (
        forall 
            data: AttestationData, 
            sig_shares: set<BLSSignature> 
            ::
                var constructed_sig := s.construct_signed_attestation_signature(data, sig_shares);
                constructed_sig.isPresent() ==> verify_bls_siganture(data, constructed_sig.get(), s.dv_pubkey)

    )   
    && s.attestations_shares_sent == {}
    && s.consensus_on_attestation_data == (imap s: Slot :: DVSAttestationConsensusData(None, {}))
    && s.slashing_dbs_used_for_validating_attestations == (imap s: Slot :: {})
    && s.aggregated_attestations_sent == {}
    && s.attestation_duties_served == map[]
    && no_slashing_conditions_in_the_slashing_db(initial_slashing_db)    
    && (
        forall p | p in s.honest_nodes_states.Values ::
            p == ServeAttesationProcess(
                attestation_duty := p.attestation_duty,
                construct_signed_attestation_signature := s.construct_signed_attestation_signature,
                slashing_db := initial_slashing_db,
                signature_shares_db := map[]
            )
    )
}

predicate DSVNext(
    s: DSVState,
    node_taking_step: BLSPubkey,
    attestation_consensus_instance: Slot,
    decided_attestation_data: AttestationData,
    slashing_db_used_to_check_attestation_data: AttestationSlashingDB,
    attestation_signature_share_received: AttestationShare,
    attestation_duty_to_be_served: AttestationDuty,
    s': DSVState
)
{
    && node_taking_step in s.all_nodes
    && (
        || (
            && node_taking_step in s.honest_nodes_states.Keys
            && s'.honest_nodes_states.Keys == s.honest_nodes_states.Keys
            && s'.honest_nodes_states == s.honest_nodes_states[node_taking_step := s'.honest_nodes_states[node_taking_step]]

            && (
                || (
                    && (forall atd | atd in s.attestation_duties_served.Keys :: atd.slot == attestation_duty_to_be_served.slot ==> atd == attestation_duty_to_be_served)
                    && (
                        || attestation_duty_to_be_served !in s.attestation_duties_served.Keys 
                        || node_taking_step !in s.attestation_duties_served[attestation_duty_to_be_served] 
                    )
                    && var process_output := f_serve_attestation_duty_start(
                        s.honest_nodes_states[node_taking_step],
                        attestation_duty_to_be_served
                    );
                    && s'.attestation_duties_served.Keys == s.attestation_duties_served.Keys + {attestation_duty_to_be_served}
                    && var s_attestation_duty_to_be_served := getOrDefault(s.attestation_duties_served, attestation_duty_to_be_served, {}); 
                    && s'.attestation_duties_served[attestation_duty_to_be_served] == s_attestation_duty_to_be_served + {node_taking_step}
                    && var consensus_id := process_output.start_consensus_with_instance_id;
                    && s'.consensus_on_attestation_data == s.consensus_on_attestation_data[consensus_id := s'.consensus_on_attestation_data[consensus_id]]
                    && s'.consensus_on_attestation_data[consensus_id].honest_nodes_running == s.consensus_on_attestation_data[consensus_id].honest_nodes_running + {node_taking_step}
                    && s'.consensus_on_attestation_data[consensus_id] == s.consensus_on_attestation_data[consensus_id].(
                        honest_nodes_running := s'.consensus_on_attestation_data[consensus_id].honest_nodes_running
                    )
                    && s'.honest_nodes_states[node_taking_step] == process_output.new_process_state
                    && s' == s.(
                        honest_nodes_states := s'.honest_nodes_states,
                        consensus_on_attestation_data := s'.consensus_on_attestation_data,
                        slashing_dbs_used_for_validating_attestations := s'.slashing_dbs_used_for_validating_attestations
                    )
                )                
                || (
                    && node_taking_step in s.consensus_on_attestation_data[attestation_consensus_instance].honest_nodes_running
                    && s'.consensus_on_attestation_data == s.consensus_on_attestation_data[attestation_consensus_instance := s'.consensus_on_attestation_data[attestation_consensus_instance]]
                    && (
                        || (
                            && s.consensus_on_attestation_data[attestation_consensus_instance].decided_value.isPresent()
                            && s.consensus_on_attestation_data[attestation_consensus_instance].decided_value.get() == decided_attestation_data
                        )
                        || (
                            && !s.consensus_on_attestation_data[attestation_consensus_instance].decided_value.isPresent()
                            && s'.consensus_on_attestation_data[attestation_consensus_instance].decided_value.isPresent()
                            && s'.consensus_on_attestation_data[attestation_consensus_instance].decided_value.get() == decided_attestation_data
                            && consensus_is_valid_attestation_data(slashing_db_used_to_check_attestation_data, decided_attestation_data, s.honest_nodes_states[node_taking_step].attestation_duty)
                        )
                    )
                    && s'.consensus_on_attestation_data[attestation_consensus_instance].honest_nodes_running == s.consensus_on_attestation_data[attestation_consensus_instance].honest_nodes_running
                    && var process_output := f_serve_attestation_duty_consensus_finished(
                        s.honest_nodes_states[node_taking_step],
                        decided_attestation_data   
                    );
                    && s'.honest_nodes_states[node_taking_step] == process_output.new_process_state
                    && s'.attestations_shares_sent == s.attestations_shares_sent + {process_output.signature_share}
                    && s' == s.(
                        honest_nodes_states := s'.honest_nodes_states,
                        attestations_shares_sent := s'.attestations_shares_sent,
                        consensus_on_attestation_data := s'.consensus_on_attestation_data,
                        slashing_dbs_used_for_validating_attestations := s'.slashing_dbs_used_for_validating_attestations
                    )
                )
                || (
                    && attestation_signature_share_received in s.attestations_shares_sent
                    && var process_output := f_listen_for_attestation_signature_shares(
                        s.honest_nodes_states[node_taking_step],
                        attestation_signature_share_received
                    );
                    && s'.honest_nodes_states[node_taking_step] == process_output.new_process_state
                    && s'.aggregated_attestations_sent == s.aggregated_attestations_sent + process_output.aggregated_attestations
                    && s' == s.(
                        honest_nodes_states := s'.honest_nodes_states,
                        aggregated_attestations_sent := s'.aggregated_attestations_sent,
                        slashing_dbs_used_for_validating_attestations := s'.slashing_dbs_used_for_validating_attestations                     
                    )
                )
            )
            && (
                forall consensus_id
                    ::
                    s'.slashing_dbs_used_for_validating_attestations[consensus_id] == s.slashing_dbs_used_for_validating_attestations[consensus_id] +
                        if node_taking_step in s'.consensus_on_attestation_data[consensus_id].honest_nodes_running then
                            {s'.honest_nodes_states[node_taking_step].slashing_db}
                        else
                            {}
            )
            
        )
        || (
            && s.attestations_shares_sent <= s'.attestations_shares_sent
            && var new_attestation_shares_sent := s'.attestations_shares_sent - s.attestations_shares_sent;
            && node_taking_step in s.adversary.nodes
            && (
                forall new_attestation_share_sent, signer | new_attestation_share_sent in new_attestation_shares_sent ::
                    verify_bls_siganture(new_attestation_share_sent.data, new_attestation_share_sent.signature, signer) ==> signer in s.adversary.nodes
            )
            && s.aggregated_attestations_sent <= s'.aggregated_attestations_sent
            && var new_aggregated_attestations_sent := s'.aggregated_attestations_sent - s.aggregated_attestations_sent;
            && (forall aggregated_attestation_sent | aggregated_attestation_sent in new_aggregated_attestations_sent ::
                    exists attestation_shares ::
                            && attestation_shares <= s'.attestations_shares_sent
                            && var sig_shares := set x | x in attestation_shares :: x.signature;
                            && var constructed_sig := s.construct_signed_attestation_signature(aggregated_attestation_sent.data, sig_shares);
                            && constructed_sig.isPresent()
                            && constructed_sig.get() == aggregated_attestation_sent.signature
            )
            && s' == s.(
                honest_nodes_states := s'.honest_nodes_states,
                attestations_shares_sent := s'.attestations_shares_sent,
                consensus_on_attestation_data := s'.consensus_on_attestation_data,
                aggregated_attestations_sent := s'.aggregated_attestations_sent
            )            
        )    
    )
}




