
module DVC
{
    type ValidatorIndex = nat
    type Epoch(==)
    type Slot(==)
    type CommitteeIndex
    type Attestation 
    type BLSSignature
    type BLSPubkey
    type Bytes32
    type SignedBeaconBlock
    type Root 
    type SyncCommitteeSignature
    // type AttestationDuty 
    type AttestationData
    // type ProposerDuty
    type BeaconBlock(==)
    type SyncCommitteeDuty   
    type Version


    datatype BNOutMessage = 
        |   GetGenesis()
        |   GetForkVersion(
                slot: Slot
            )
        |   GetAttestationDutiesForEpoch(
                validator_indices: seq<ValidatorIndex>,
                epoch: Epoch
            )
        |   ProduceAttestationData(
                slot: Slot,
                commitee_index: CommitteeIndex
            )
        |   SubmitAttestation(
                attesatation: Attestation
            )
        |   GetProposerDutiesForEpoch(
                epoch: Epoch
            )
        |   ProduceBlock(
                slot: Slot,
                randao_reveal: BLSSignature,
                graffiti: Bytes32
            )
        |   SubmitBlock( 
                block: SignedBeaconBlock
            )      

    datatype BNInMessage = 
        |   GetGenesisResponse(
                genesis_time: nat,
                genesis_validator_root: Root,
                genesis_fork_version: Version
            )
        |   GetForkVersionResponse(
                version: Version
            )    
        |   GetAttestationDutiesForEpochResponse(
                attestation_duties: seq<AttestationDuty>
            )
        |   ProduceAttestationDataResponse(
                attestation_data: AttestationData
            )
        |   GetProposerDutiesForEpochResponse(
                proposer_duties: seq<ProposerDuty>
            )
        |   ProduceBlockResponse(
                beacon_block: BeaconBlock
            )

    datatype RSOutMessage = 
        |   SignAttestation(
                attestation_data: AttestationData,
                fork_version: Version,
                signing_root: Root
            )
        |   SignaRandaoReveal(
                epoch: Epoch,
                fork_version: Version,
                signing_root: Root
            )
        |   SignBlock(
                block: BeaconBlock,
                fork_version: Version,
                signing_root: Root
            )

    datatype RSInMessage = 
        |   SignAttestationResponse(
                bls_signature: BLSSignature
            )
        |   SignaRandaoRevealResponse(
                bls_signature: BLSSignature
            )
        |   SignBlockResponse(
                bls_signature: BLSSignature
            )            


    datatype SlashingDB = SlashingDB

    datatype ConsensusCommands<I, !T> = 
    |   StartConsensus(
            instance_id: I,
            initial_value: T,
            validity_function: T -> bool
        )
    |   StopConsensus(
            instance_id: I
        )

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

    datatype ProposerDuty = ProposerDuty(
        pubkey: BLSPubkey,
        validator_index: ValidatorIndex,
        slot: Slot        
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

    datatype ConsenusCallback<I, T> = ConsenusCallback(
        instance_id: I,
        decided_value: Optional<T>
    )

    datatype Duty = 
    |   AttestationSigningDuty(
            slot: Slot,
            commitee_index: CommitteeIndex        
        )
    |   BlockProductionDuty(

        )

    datatype TimerEvent = 
    |   EpochStart(
        )
    |   ProposerDutyServe(
            proposer_duty: ProposerDuty
        )
    |   AttestationDutyServe(
            attestation_duty: AttestationDuty
        )        

    datatype Event = 
    |   Timer(timer_event: TimerEvent)
    |   BNInMessage(bn_in_message: BNInMessage)
    |   RSInMessage(rs_in_message: RSInMessage)

    datatype TimerSetup = TimerSetup(
        timer_event: TimerEvent,
        expiry_time: nat
    )

    datatype NewStateOutputsAndTimers = NewStateOutputsAndTimers(
        newState: DVCState,
        BNOutMessages: seq<BNOutMessage>, // This should probably be a set
        RSOutMessage: seq<RSOutMessage>,  // This should probably be a set
        attestationConsensusStartCommands: seq<ConsensusCommands<Slot, AttestationData>>, // This should probably be a set
        blockProductionConsensusStartCommands: seq<ConsensusCommands<Slot, BeaconBlock>>, // This should probably be a set
        timers_to_be_setup: set<TimerSetup>
    )


    function mapSeq<T1, T2>(
        s: seq<T1>,
        f: T1 -> T2
    ): (ret: seq<T2>)
    {
        seq(|s|, (i:nat) requires i < |s| => f(s[i]))
    }


    datatype Configuration = Configuration(
        distributed_validators_configurations: seq<DistributedValidatorInitialConfiguration>
    )
   

    function InitDistributedValidatorState(
        configuration: DistributedValidatorInitialConfiguration
    ): DistributeValidatorState
    {
        var anyAttestorState: DistributedAttestoorState :| true;
        var anyBlockProducerState: DistributeBlockProducerState :| true;
        DistributeValidatorState(
            configuration := configuration,
            attestor_state := anyAttestorState,
            block_producer_state := anyBlockProducerState,
            slashing_db := configuration.initial_slashing_db
        )
    }

    function Init(
        configuration: Configuration
    ): NewStateOutputsAndTimers
    requires validConfiguration(configuration)
    {
        NewStateOutputsAndTimers(
            newState := DVCState(
                distributed_validator_states := 
                    map i | 0 <= i < |configuration.distributed_validators_configurations| 
                        ::
                    configuration.distributed_validators_configurations[i].validator_identity.index := InitDistributedValidatorState(configuration.distributed_validators_configurations[i]),
                    // mapSeq(configuration.distributed_validators_configurations, InitDistributedValidatorState),
                step := STEP_INIT,
                genesis_time := None
            ),
            BNOutMessages := [
                GetGenesis()
            ],
            RSOutMessage := [],
            attestationConsensusStartCommands := [],
            blockProductionConsensusStartCommands := [],
            timers_to_be_setup := {}
        )
    }

    // function fTestMatch(i: int): int
    // {
    //         match i {
    //             case 0 => 1
    //             case 1 => 2
    //             case -3 => 4
    //             case default => 10
    //         }     
    // }

    // lemma lTestMatch()
    // {
    //     // var i: int :| true;

    //     assert fTestMatch(0) == 1;
    //     assert fTestMatch(-3) == 4;
    //     assert fTestMatch(-4) == 10;


        
    // }

    datatype DVCStep = 
    |   STEP_INIT
    |   STEP_WAIT_EPOCH_START
    |   STEP_WAIT_FOR_LIST_OF_DUTIES
    |   STEP_WAIT_FOR_DUTIES_TO_BE_SERVED

    datatype AttestorStep = 
    |   STEP_1

    datatype BlockProducerStep = 
    |   STEP_WAIT_GET_FORK_VERSION

    // Identity of the Ethereum validator.
    datatype ValidatorIdentity = ValidatorIdentity(
        // Ethereum public key
        pubkey: BLSPubkey,
        // Index of Ethereum validator
        index: ValidatorIndex
    )

    // Identity of distributed co-validator participating in the DV protocol.
    datatype CoValidatorIdentity = CoValidatorIdentity(
        // Identity of Ethereum validator that this co-validator performs duties for
        // validator_identity: ValidatorIdentity,
        // Secret-shared public key
        pubkey: BLSPubkey,
        // Index of the co-validator in the distributed validator protocol
        index: ValidatorIndex
    )

    datatype DistributedValidatorInitialConfiguration = DistributedValidatorInitialConfiguration(
        validator_identity: ValidatorIdentity,
        co_validators: seq<CoValidatorIdentity>,
        initial_slashing_db: SlashingDB
        // ,
        // step: DVCStep,
        // genesis_time: Optional<nat>        
    )

    datatype DistributedAttestoorState = DistributedAttestoorState(
        step: AttestorStep
    )

    datatype DistributeBlockProducerState = DistributedBlockProducerState(
        step: BlockProducerStep
    )

    datatype DistributeValidatorState = DistributeValidatorState(
        configuration: DistributedValidatorInitialConfiguration,
        attestor_state: DistributedAttestoorState,
        block_producer_state: DistributeBlockProducerState,
        slashing_db: SlashingDB
    )

    datatype DVCState = DVCState(
            // slashing_db: SlashingDB,
            step: DVCStep,
            genesis_time: Optional<nat>,
            // distributed_validator_states: seq<DistributeValidatorState>
            distributed_validator_states: map<ValidatorIndex, DistributeValidatorState>
        ) 

    function setToSeq<T(!new)>(s:set<T>):seq<T>
    {
        if s == {} then
            []
        else
            var e :| e in s;
            setToSeq(s - {e}) +
            [e]
    }        

    // Q: Does the list of ValidatorIndex need to be ordered?
    function get_validator_indices(state: DVCState): seq<ValidatorIndex>
    {
        // mapSeq( state.distributed_validator_states,
        //         (distributed_validator_state: DistributeValidatorState) => distributed_validator_state.configuration.validator_identity.index)
        setToSeq(state.distributed_validator_states.Keys)
    }

    function get_curent_epoch(genesis_time: nat, current_time: nat): Epoch

    function getNextEpochTimeBoundry(genesis_time:nat, current_time:nat): (next_epoch_time_boundry: nat)

    function getProposerDutyServeTime(genesis_time:nat, epoch: Epoch, slot: Slot): (slot_start_time: nat)

    function getAttestationsDutyServeTime(genesis_time:nat, epoch: Epoch, slot: Slot): (one_third_after_slot_start: nat)

    predicate validDVCState(
        dvc_state: DVCState
    )
    {
        && (forall i, j | i in dvc_state.distributed_validator_states && j in dvc_state.distributed_validator_states && i != j :: 
            dvc_state.distributed_validator_states[i].configuration.validator_identity.index != dvc_state.distributed_validator_states[j].configuration.validator_identity.index)

        // forall distributed_validator_state | distributed_validator_state in dvc_state.distributed_validator_states.Values :: validConfiguration(distributed_validator_state.configuration)
    }

    predicate validConfiguration(
        configuration: Configuration
    )
    {
        && (forall i, j | 0 <= i < j < |configuration.distributed_validators_configurations| :: 
            configuration.distributed_validators_configurations[i].validator_identity.index != configuration.distributed_validators_configurations[j].validator_identity.index)        
    }

    predicate validator_index_is_one_of_ours(
        dvc_state: DVCState,
        validator_index: nat 
    )
    {
        // exists i | 0 <= i < |dvc_state.distributed_validator_states| :: dvc_state.distributed_validator_states[i].configuration.validator_identity.index == validator_index

        validator_index in dvc_state.distributed_validator_states.Keys
    }

    // function getDistributedValidatorStateByIndex(
    //     dvc_state: DVCState,
    //     validator_index: nat
    // ): DistributeValidatorState
    // requires validator_index_is_one_of_ours(dvc_state, validator_index)
    // {
    //     // var i :| 0 <= i < |dvc_state.distributed_validator_states| && dvc_state.distributed_validator_states[i].configuration.validator_identity.index == validator_index;
    //     // dvc_state.distributed_validator_states[i]

    // }


    predicate isProposerDutyForUs(
        dvc_state: DVCState,
        proposer_duty: ProposerDuty
    )
    {
        // exists distributed_validator_state: DistributeValidatorState ::
        //     && distributed_validator_state in dvc_state.distributed_validator_states
        //     && proposer_duty.validator_index == distributed_validator_state.configuration.validator_identity.index
        //     && proposer_duty.pubkey == distributed_validator_state.configuration.validator_identity.pubkey

        && proposer_duty.validator_index in dvc_state.distributed_validator_states
        && dvc_state.distributed_validator_states[proposer_duty.validator_index].configuration.validator_identity.pubkey == proposer_duty.pubkey
    }

    predicate isAttestationDutyForUs(
        dvc_state: DVCState,
        attestation_duty: AttestationDuty
    )
    {
        // exists distributed_validator_state: DistributeValidatorState ::
        //     && distributed_validator_state in dvc_state.distributed_validator_states
        //     && attestation_duty.validator_index == distributed_validator_state.configuration.validator_identity.index
        //     && attestation_duty.pubkey == distributed_validator_state.configuration.validator_identity.pubkey
        && attestation_duty.validator_index in dvc_state.distributed_validator_states
        && dvc_state.distributed_validator_states[attestation_duty.validator_index].configuration.validator_identity.pubkey == attestation_duty.pubkey        
    }    

    function setNewDistributedValidatorState(
        dvc_state: DVCState,
        validator_index: ValidatorIndex,
        new_distributed_validator_state: DistributeValidatorState
    ): (new_dvc_state: DVCState)
    {
        dvc_state.(
            distributed_validator_states := dvc_state.distributed_validator_states[
                validator_index := new_distributed_validator_state
            ]
        )
    }

    function setNewDistributedBlockProducerState(
        dvc_state: DVCState,
        validator_index: ValidatorIndex,
        new_distributed_block_producer_state: DistributeBlockProducerState
    ): DVCState
    requires validator_index in dvc_state.distributed_validator_states
    {
        var distributed_validator_state := dvc_state.distributed_validator_states[validator_index];
            // getDistributedValidatorStateByIndex(dvc_state, attestation_duty.validator_index);

        var new_distributed_validator_state := distributed_validator_state.(
            block_producer_state := new_distributed_block_producer_state
        ); 

        setNewDistributedValidatorState(dvc_state, validator_index, new_distributed_validator_state)   
    }

    function HandleEvent(dvc_state: DVCState, event: Event, current_time: nat): NewStateOutputsAndTimers
    requires dvc_state.step.STEP_INIT? ==> event.BNInMessage? && event.bn_in_message.GetGenesisResponse?
    requires dvc_state.step.STEP_WAIT_EPOCH_START? ==>  && event.Timer? 
                                                        && event.timer_event.EpochStart?
                                                        && dvc_state.genesis_time.isPresent()
    {
       var dummyRet: NewStateOutputsAndTimers :| true; 

        match dvc_state.step 
        {
            case STEP_INIT =>
                match event
                {
                    case BNInMessage(message) =>
                        match message
                        {
                            case GetGenesisResponse(
                                genesis_time,
                                _,
                                _
                            ) =>  
                                NewStateOutputsAndTimers(
                                    newState := dvc_state.(
                                        step := STEP_WAIT_EPOCH_START,
                                        genesis_time := Some(genesis_time)
                                    ),
                                    BNOutMessages := [],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := {
                                        TimerSetup(
                                            timer_event := EpochStart(),
                                            expiry_time := getNextEpochTimeBoundry(genesis_time, current_time)
                                        )
                                    }
                                )
                        }
                }


            case STEP_WAIT_EPOCH_START =>
                match event
                {
                    case Timer(timer_event) =>
                        match timer_event
                        {
                            case EpochStart =>  
                                NewStateOutputsAndTimers(
                                    newState := dvc_state.(
                                        step := STEP_WAIT_FOR_LIST_OF_DUTIES
                                    ),
                                    BNOutMessages := [
                                        GetAttestationDutiesForEpoch(
                                            validator_indices := get_validator_indices(dvc_state),
                                            epoch := get_curent_epoch(dvc_state.genesis_time.get(), current_time)
                                        ),
                                        GetProposerDutiesForEpoch(
                                            epoch := get_curent_epoch(dvc_state.genesis_time.get(), current_time)
                                        )                                        
                                    ],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := {
                                        TimerSetup(
                                            timer_event := EpochStart(),
                                            expiry_time := getNextEpochTimeBoundry(dvc_state.genesis_time.get(), current_time)
                                        )                                        
                                    }
                                )
                        }
                } 

            case STEP_WAIT_FOR_LIST_OF_DUTIES =>
                match event
                {
                    case BNInMessage(message) =>
                        match message
                        {
                            case GetProposerDutiesForEpochResponse(
                                    proposer_duties
                            ) =>  
                                NewStateOutputsAndTimers(
                                    newState := dvc_state.(
                                        step := STEP_WAIT_FOR_DUTIES_TO_BE_SERVED
                                    ),
                                    BNOutMessages := [],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := 
                                        set proposer_duty | 
                                            && proposer_duty in proposer_duties 
                                            && isProposerDutyForUs(dvc_state, proposer_duty)
                                            ::
                                            TimerSetup(
                                                ProposerDutyServe(proposer_duty),
                                                getProposerDutyServeTime(
                                                    dvc_state.genesis_time.get(),
                                                    get_curent_epoch(dvc_state.genesis_time.get(), current_time),
                                                    proposer_duty.slot
                                                )
                                            )
                                )

                            case GetAttestationDutiesForEpochResponse(
                                    attestation_duties
                            ) =>  
                                NewStateOutputsAndTimers(
                                    newState := dvc_state.(
                                        step := STEP_WAIT_FOR_DUTIES_TO_BE_SERVED
                                    ),
                                    BNOutMessages := [],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := 
                                        set attestation_duty | 
                                            && attestation_duty in attestation_duties 
                                            && isAttestationDutyForUs(dvc_state, attestation_duty)
                                            ::
                                            TimerSetup(
                                                AttestationDutyServe(attestation_duty),
                                                getAttestationsDutyServeTime(
                                                    dvc_state.genesis_time.get(),
                                                    get_curent_epoch(dvc_state.genesis_time.get(), current_time),
                                                    attestation_duty.slot
                                                )
                                            )
                                )   

                            case default =>
                                NewStateOutputsAndTimers(
                                    newState := dvc_state,
                                    BNOutMessages := [],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := {}
                                )                                                             
                        }

                    case default => 
                        NewStateOutputsAndTimers(
                            newState := dvc_state,
                            BNOutMessages := [],
                            RSOutMessage := [],
                            attestationConsensusStartCommands := [],
                            blockProductionConsensusStartCommands := [],
                            timers_to_be_setup := {}
                        )                        
                }   

            case STEP_WAIT_FOR_DUTIES_TO_BE_SERVED =>
                match event
                {
                    case Timer(timer_event) =>
                        match timer_event
                        {
                            case ProposerDutyServe(proposer_duty) =>  
                                var block_producer_state := dvc_state.distributed_validator_states[proposer_duty.validator_index].block_producer_state;
                                    // getDistributedValidatorStateByIndex(dvc_state, attestation_duty.validator_index);

                                var new_block_producer_state := block_producer_state.(
                                    step := STEP_WAIT_GET_FORK_VERSION
                                );

                                // var block_producer_state := distributed_validator_state.block_producer_state;

                                // var new_distributed_validator_state := distributed_validator_state.(
                                //     block_producer_state := block_producer_state.(
                                //         step := STEP_WAIT_GET_FORK_VERSION
                                //     )
                                // );

                                NewStateOutputsAndTimers(
                                    newState := setNewDistributedBlockProducerState(
                                        dvc_state,
                                        proposer_duty.validator_index,
                                        new_block_producer_state
                                    ),
                                    BNOutMessages := [
                                        GetForkVersion(proposer_duty.slot)
                                    ],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := {}
                                )      

                            case AttestationDutyServe(attestation_duty) =>

                                NewStateOutputsAndTimers(
                                    newState := dvc_state,
                                    BNOutMessages := [],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := {}
                                ) 

                            case default =>
                                NewStateOutputsAndTimers(
                                    newState := dvc_state,
                                    BNOutMessages := [],
                                    RSOutMessage := [],
                                    attestationConsensusStartCommands := [],
                                    blockProductionConsensusStartCommands := [],
                                    timers_to_be_setup := {}
                                )                                                           
                        }
                    
                    case default => 
                        NewStateOutputsAndTimers(
                            newState := dvc_state,
                            BNOutMessages := [],
                            RSOutMessage := [],
                            attestationConsensusStartCommands := [],
                            blockProductionConsensusStartCommands := [],
                            timers_to_be_setup := {}
                        )                        
                }                          
                
        }       
    }


    // function HandleBNMessage(dvc_state: DVCState, m: BNInMessage, current_time: nat): NewStateOutputsAndTimers
    // requires dvc_state.step.STEP_INIT? ==> m.GetGenesisResponse?
    // {
    //     var dummyRet: NewStateOutputsAndTimers :| true;

    //     match dvc_state.step 
    //     {
    //         case STEP_INIT =>
    //             match m 
    //             {
    //                 case GetGenesisResponse(
    //                     genesis_time,
    //                     genesis_validator_root,
    //                     genesis_fork_version
    //                 ) =>  
    //                     NewStateOutputsAndTimers(
    //                         newState := dvc_state.(
    //                             step := STEP_WAIT_EPOCH_START
    //                         ),
    //                         BNOutMessages := [],
    //                         RSOutMessage := [],
    //                         attestationConsensusStartCommands := [],
    //                         blockProductionConsensusStartCommands := [],
    //                         timers_to_be_setup := {
    //                             TimerSetup(
    //                                 timer_event := EpochStart(),
    //                                 expiry_time := getNextEpochTimeBoundry(current_time)
    //                             )
    //                         }
    //                     )
    //             }

    //         case STEP_WAIT_EPOCH_START =>
    //             dummyRet
    //     }

    //     // NewStateOutputsAndTimers(
    //     //     newState := s.(

    //     //     ),
    //     //     BNOutMessages := [
    //     //         GetGenesis()
    //     //     ],
    //     //     BNInMessages := [],
    //     //     attestationConsensusStartCommands := [],
    //     //     blockProductionConsensusStartCommands := [],
    //     //     timers_to_be_setup := {}
    //     // )
    // }

    // function HandleRSMessage(s: DVCState, m: RSInMessage): NewStateOutputsAndTimers

    // function HandleBlockProductionConsensusCallback(s: DVCState, cb: ConsenusCallback<Slot, BeaconBlock>): NewStateOutputsAndTimers

    // function HandleAttestationsConsensusCallback(s: DVCState, cb: ConsenusCallback<Slot, AttestationData>): NewStateOutputsAndTimers  

    // function update_attestation_slashing_db(slashing_db: SlashingDB, attestation_data: AttestationData, pubkey: BLSPubkey): SlashingDB

    // function update_block_slashing_db(slashing_db: SlashingDB, block: BeaconBlock, pubkey: BLSPubkey): SlashingDB


    // function HandleSyncCommitteeConsensusCallback(s: DVCState, cb: ConsenusCallback<(Slot, ValidatorIndex, Root),SyncCommitteeSignature>): NewStateOutputsAndTimers  

    // function HandleBlockProductionDuty  


    
}



