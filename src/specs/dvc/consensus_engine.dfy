include "../../common/commons.dfy"

module Consensus_Engine_NonInstr
{
    import opened Types 
    import opened CommonFunctions

    datatype ConsensusEngineState<T(!new)> = ConsensusEngineState(
        active_consensus_instances: map<Slot, T>
    )
    
    function getInitialBlockConensusEngineState(): ConsensusEngineState<BlockConsensusValidityCheckState>
    {
        ConsensusEngineState(
            active_consensus_instances := map[]
        )
    }

    function startBlockConsensusInstance(
        s: ConsensusEngineState<BlockConsensusValidityCheckState>,
        slot: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature
    ): ConsensusEngineState<BlockConsensusValidityCheckState>
    requires slot !in s.active_consensus_instances.Keys    
    requires slot == proposer_duty.slot
    {
        var bcvc := 
            BlockConsensusValidityCheckState(
                    proposer_duty := proposer_duty,
                    randao_reveal := complete_signed_randao_reveal,
                    validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    proposer_duty,
                                                                    complete_signed_randao_reveal)
            );
        
        assert (bcvc.validityPredicate == ((block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    bcvc.proposer_duty,
                                                                    bcvc.randao_reveal)));                
        s.(
            active_consensus_instances := s.active_consensus_instances[
                slot := bcvc
            ]
        )
    }

    function stopBlockConsensusInstances(
        s: ConsensusEngineState<BlockConsensusValidityCheckState>,
        ids: set<Slot>
    ): ConsensusEngineState<BlockConsensusValidityCheckState>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }

    function updateBlockConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (r: map<Slot, BlockConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    new_block_slashing_db, 
                                                                    block, 
                                                                    it.1.proposer_duty,
                                                                    it.1.randao_reveal 
                                                                 )
                )        
    } 

    function updateBlockConsensusInstanceValidityCheck(
        s: ConsensusEngineState<BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (r: ConsensusEngineState<BlockConsensusValidityCheckState>)
    ensures r.active_consensus_instances.Keys <= s.active_consensus_instances.Keys
    {
        var new_active_consensus_instances := updateBlockConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances,
                    new_block_slashing_db
                );
        s.(
            active_consensus_instances := new_active_consensus_instances                
        )
    }

    function getAttInitialConensusEngineState(): ConsensusEngineState<AttestationConsensusValidityCheckState>
    {
        ConsensusEngineState(
            active_consensus_instances := map[]
        )
    }

    function startAttConsensusInstance(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState>,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>
    ): ConsensusEngineState<AttestationConsensusValidityCheckState>
    requires id !in s.active_consensus_instances.Keys
    {
        var acvc := AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
                );
        
        assert (acvc.validityPredicate == (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, acvc.attestation_duty));
        
        var new_active_consensus_instances := 
                s.active_consensus_instances[
                    id := acvc
                ];

        s.(
            active_consensus_instances := new_active_consensus_instances
        )
    }

    function stopAttConsensusInstances(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState>,
        ids: set<Slot>
    ): ConsensusEngineState<AttestationConsensusValidityCheckState>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }    


    function updateAttConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(new_attestation_slashing_db, ad, it.1.attestation_duty)
                )        
    }

    function updateAttConsensusInstanceValidityCheck(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: ConsensusEngineState<AttestationConsensusValidityCheckState>)
    {
        var new_active_consensus_instances := 
            updateAttConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );

        s.(
            active_consensus_instances := new_active_consensus_instances
        )
    }
}

module Consensus_Engine_Instr
{
    import opened Types 
    import opened CommonFunctions

    datatype ConsensusEngineState<T1(!new), !T2(!new, ==), T3(!new, ==)> = ConsensusEngineState(
        active_consensus_instances: map<Slot, T1>,
        ghost slashing_db_hist: map<Slot, map<T2 -> bool, set<set<T3>>>>
    )

    function getInitialBlockConensusEngineState(): ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    {
        ConsensusEngineState(
            active_consensus_instances := map[],
            slashing_db_hist := map[]
        )
    }

    function startBlockConsensusInstance(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        slot: Slot,
        proposer_duty: ProposerDuty,
        block_slashing_db: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature
    ): ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    requires slot !in s.active_consensus_instances.Keys    
    requires slot == proposer_duty.slot
    {
        var bcvc := 
            BlockConsensusValidityCheckState(
                    proposer_duty := proposer_duty,
                    randao_reveal := complete_signed_randao_reveal,
                    validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    proposer_duty,
                                                                    complete_signed_randao_reveal)
            );
        
        assert (bcvc.validityPredicate == ((block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    block_slashing_db, 
                                                                    block, 
                                                                    bcvc.proposer_duty,
                                                                    bcvc.randao_reveal)));                
        
        var new_active_consensus_instances := 
            s.active_consensus_instances[
                slot := bcvc
            ];

        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := 
                addToBlockSlashingDBHist(
                    s.slashing_db_hist,
                    slot,
                    bcvc.validityPredicate,
                    block_slashing_db                    
                )
                
        )
    }

    function addToBlockSlashingDBHist(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        id: Slot,
        vp: BeaconBlock -> bool,
        block_slashing_db: set<SlashingDBBlock>
    ): (new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>)
    ensures hist.Keys + { id } == new_hist.Keys
    ensures ( forall slot0, vp0 ::
                    && var hist_slot0 := getOrDefault(hist, slot0, map[]);
                    && var hist_slot_vp0 := getOrDefault(hist_slot0, vp0, {});
                    && var new_hist_slot0 := getOrDefault(new_hist, slot0, map[]);
                    && var new_hist_slot_vp0 := getOrDefault(new_hist_slot0, vp0, {});
                    && (( slot0 != id || vp0 != vp )
                        ==> 
                        hist_slot_vp0 == new_hist_slot_vp0
                        )
                    && ((slot0 == id && vp0 == vp )
                        ==> 
                        hist_slot_vp0 + {block_slashing_db} == new_hist_slot_vp0
                        )
            )
    {
        var hist_id := getOrDefault(hist, id, map[]);
        var new_hist_id_vp := getOrDefault(hist_id, vp, {}) + {block_slashing_db};
        hist[
            id := hist_id[
                vp := new_hist_id_vp
            ]
        ]
    }  


    function stopBlockConsensusInstances(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        ids: set<Slot>
    ): ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }    
 
    function updateBlockSlashingDBHist(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        new_active_consensus_instances : map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>)
    ensures hist.Keys + new_active_consensus_instances.Keys == new_hist.Keys
    ensures ( forall s, vp | s in hist.Keys && vp in hist[s].Keys ::
                && s in new_hist.Keys 
                && vp in new_hist[s].Keys
                && hist[s][vp] <= new_hist[s][vp]
            )
    {
            var ret 
                := 
                map k: Slot | k in (new_active_consensus_instances.Keys + hist.Keys)
                    ::            
                    if k in new_active_consensus_instances.Keys then 
                        var vp := new_active_consensus_instances[k].validityPredicate;
                        var hist_k := getOrDefault(hist, k, map[]);
                        var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_block_slashing_db};
                        hist_k[
                            vp := hist_k_vp
                        ]
                    else
                        hist[k];
            ret
    }

    function updateBlockConsensusInstanceValidityCheckHelper(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (r: map<Slot, BlockConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    ensures (forall k: Slot | k in r.Keys
                ::
                &&  m[k].proposer_duty == r[k].proposer_duty
                && var vp := r[k].validityPredicate;
                && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                        new_block_slashing_db, 
                                                        block, 
                                                        r[k].proposer_duty,
                                                        r[k].randao_reveal 
                                                    )
                );
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    new_block_slashing_db, 
                                                                    block, 
                                                                    it.1.proposer_duty,
                                                                    it.1.randao_reveal 
                                                                 )
                )        
    } 

    function updateBlockConsensusInstanceValidityCheck(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        new_block_slashing_db: set<SlashingDBBlock>
    ): (r: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>)
    ensures && var new_active_consensus_instances := updateBlockConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances,
                    new_block_slashing_db
                );
            && s.slashing_db_hist.Keys + new_active_consensus_instances.Keys == r.slashing_db_hist.Keys
    {
        var new_active_consensus_instances := updateBlockConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances,
                    new_block_slashing_db
                );
        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := updateBlockSlashingDBHist(
                s.slashing_db_hist,
                new_active_consensus_instances,
                new_block_slashing_db
            )
        )
    }

    function getInitialAttConensusEngineState(): ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    {
        ConsensusEngineState(
            active_consensus_instances := map[],
            slashing_db_hist := map[]
        )
    }

    function startAttConsensusInstance(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>
    ): ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    requires id !in s.active_consensus_instances.Keys
    requires id == attestation_duty.slot
    {
        var acvc := 
            AttestationConsensusValidityCheckState(
                attestation_duty := attestation_duty,
                validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, attestation_duty)
            );
        
        assert (acvc.validityPredicate == (ad: AttestationData) => ci_decision_is_valid_attestation_data(attestation_slashing_db, ad, acvc.attestation_duty));
        
        var new_active_consensus_instances := 
            s.active_consensus_instances[
                id := acvc
            ];

        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := 
                addToAttSlashingDBHist(
                    s.slashing_db_hist,
                    id,
                    acvc.validityPredicate,
                    attestation_slashing_db                    
                )
                
        )
    }

    function addToAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        id: Slot,
        vp: AttestationData -> bool,
        attestation_slashing_db: set<SlashingDBAttestation>
    ): (new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>)
    ensures hist.Keys + { id } == new_hist.Keys
    ensures ( forall slot0, vp0 ::
                    && var hist_slot0 := getOrDefault(hist, slot0, map[]);
                    && var hist_slot_vp0 := getOrDefault(hist_slot0, vp0, {});
                    && var new_hist_slot0 := getOrDefault(new_hist, slot0, map[]);
                    && var new_hist_slot_vp0 := getOrDefault(new_hist_slot0, vp0, {});
                    && (( slot0 != id || vp0 != vp )
                        ==> 
                        hist_slot_vp0 == new_hist_slot_vp0
                        )
                    && ((slot0 == id && vp0 == vp )
                        ==> 
                        hist_slot_vp0 + {attestation_slashing_db} == new_hist_slot_vp0
                        )
            )
    {
        var hist_id := getOrDefault(hist, id, map[]);
        var new_hist_id_vp := getOrDefault(hist_id, vp, {}) + {attestation_slashing_db};
        hist[
            id := hist_id[
                vp := new_hist_id_vp
            ]
        ]
    }  

    function stopAttConsensusInstances(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        ids: set<Slot>
    ): ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }    

    function updateConsensusInstanceValidityCheckHelper(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (ad: AttestationData) => ci_decision_is_valid_attestation_data(new_attestation_slashing_db, ad, it.1.attestation_duty)
                )        
    }
  
    function updateAttSlashingDBHist(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        new_active_consensus_instances : map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>)
    ensures hist.Keys + new_active_consensus_instances.Keys == new_hist.Keys
    {
            var ret 
                := map k: Slot | k in (new_active_consensus_instances.Keys + hist.Keys)
                    ::            
                    if k in new_active_consensus_instances.Keys then 
                        var vp := new_active_consensus_instances[k].validityPredicate;
                        var hist_k := getOrDefault(hist, k, map[]);
                        var hist_k_vp := getOrDefault(hist_k, vp, {}) + {new_attestation_slashing_db};
                        hist_k[
                            vp := hist_k_vp
                        ]
                    else
                        hist[k];
            ret
    }

    function updateAttConsensusInstanceValidityCheck(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>)
    ensures && var new_active_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );
            && s.slashing_db_hist.Keys + new_active_consensus_instances.Keys == r.slashing_db_hist.Keys
    {
        var new_active_consensus_instances := updateConsensusInstanceValidityCheckHelper(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );
        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := updateAttSlashingDBHist(
                s.slashing_db_hist,
                new_active_consensus_instances,
                new_attestation_slashing_db
            )
        )
    }
}