include "../../common/commons.dfy"

module Non_Instr_Consensus_Engine
{
    import opened Types 
    import opened Signing_Methods

    function f_initialize_block_conensus_engine_state(): NonInstrConsensusEngineState<BlockConsensusValidityCheckState>
    {
        NonInstrConsensusEngineState(
            active_consensus_instances := map[]
        )
    }

    function f_start_block_consensus_instance(
        s: NonInstrConsensusEngineState<BlockConsensusValidityCheckState>,
        slot: Slot,
        proposer_duty: ProposerDuty,
        slashing_db_blocks: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature
    ): NonInstrConsensusEngineState<BlockConsensusValidityCheckState>
    requires slot !in s.active_consensus_instances.Keys    
    requires slot == proposer_duty.slot
    {
        var bcvc := 
            BlockConsensusValidityCheckState(
                    proposer_duty := proposer_duty,
                    randao_reveal := complete_signed_randao_reveal,
                    validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    slashing_db_blocks, 
                                                                    block, 
                                                                    proposer_duty,
                                                                    complete_signed_randao_reveal)
            );
        
        assert (bcvc.validityPredicate == ((block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    slashing_db_blocks, 
                                                                    block, 
                                                                    bcvc.proposer_duty,
                                                                    bcvc.randao_reveal)));                
        s.(
            active_consensus_instances := s.active_consensus_instances[
                slot := bcvc
            ]
        )
    }

    function f_stop_block_consensus_instances(
        s: NonInstrConsensusEngineState<BlockConsensusValidityCheckState>,
        ids: set<Slot>
    ): NonInstrConsensusEngineState<BlockConsensusValidityCheckState>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }

    function f_update_block_consensus_instance_validity_check_states(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_slashing_db_blocks: set<SlashingDBBlock>
    ): (r: map<Slot, BlockConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    new_slashing_db_blocks, 
                                                                    block, 
                                                                    it.1.proposer_duty,
                                                                    it.1.randao_reveal 
                                                                 )
                )        
    } 

    function f_update_block_consensus_engine_state(
        s: NonInstrConsensusEngineState<BlockConsensusValidityCheckState>,
        new_slashing_db_blocks: set<SlashingDBBlock>
    ): (r: NonInstrConsensusEngineState<BlockConsensusValidityCheckState>)
    ensures r.active_consensus_instances.Keys <= s.active_consensus_instances.Keys
    {
        var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_slashing_db_blocks
                );
        s.(
            active_consensus_instances := new_active_consensus_instances                
        )
    }

    function f_initialize_att_consensus_engine_state(): NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>
    {
        NonInstrConsensusEngineState(
            active_consensus_instances := map[]
        )
    }

    function f_start_att_consensus_instance(
        s: NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>,
        id: Slot,
        attestation_duty: AttestationDuty,
        attestation_slashing_db: set<SlashingDBAttestation>
    ): NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>
    requires id !in s.active_consensus_instances.Keys
    {
        var acvc := AttestationConsensusValidityCheckState(
                    attestation_duty := attestation_duty,
                    validityPredicate := (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(attestation_slashing_db, ad, attestation_duty)
                );
        
        assert (acvc.validityPredicate == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(attestation_slashing_db, ad, acvc.attestation_duty));
        
        var new_active_consensus_instances := 
                s.active_consensus_instances[
                    id := acvc
                ];

        s.(
            active_consensus_instances := new_active_consensus_instances
        )
    }

    function f_stop_att_consensus_instances(
        s: NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>,
        ids: set<Slot>
    ): NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }    


    function f_update_att_consensus_instance_validity_check_states(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(new_attestation_slashing_db, ad, it.1.attestation_duty)
                )        
    }

    function f_update_att_consensus_engine_state(
        s: NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>)
    {
        var new_active_consensus_instances := 
            f_update_att_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );

        s.(
            active_consensus_instances := new_active_consensus_instances
        )
    }
}

module Consensus_Engine
{
    import opened Types 
    import opened Common_Functions
    import opened Signing_Methods

    function f_initialize_block_conensus_engine_state(): ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    {
        ConsensusEngineState(
            active_consensus_instances := map[],
            slashing_db_hist := map[]
        )
    }

    function f_start_block_consensus_instance(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        slot: Slot,
        proposer_duty: ProposerDuty,
        slashing_db_blocks: set<SlashingDBBlock>,
        complete_signed_randao_reveal: BLSSignature
    ): ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    requires slot !in s.active_consensus_instances.Keys    
    requires slot == proposer_duty.slot
    {
        var bcvc := 
            BlockConsensusValidityCheckState(
                    proposer_duty := proposer_duty,
                    randao_reveal := complete_signed_randao_reveal,
                    validityPredicate := (block: BeaconBlock) =>  ci_decision_is_valid_beacon_block(
                                                                    slashing_db_blocks, 
                                                                    block, 
                                                                    proposer_duty,
                                                                    complete_signed_randao_reveal)
            );
        
        assert (bcvc.validityPredicate == ((block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                                    slashing_db_blocks, 
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
                f_update_block_slashing_db_hist_with_new_id_and_vp(
                    s.slashing_db_hist,
                    slot,
                    bcvc.validityPredicate,
                    slashing_db_blocks                    
                )
                
        )
    }

    function f_update_block_slashing_db_hist_with_new_id_and_vp(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        id: Slot,
        vp: BeaconBlock -> bool,
        slashing_db_blocks: set<SlashingDBBlock>
    ): (new_hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>)
    ensures hist.Keys + { id } == new_hist.Keys
    ensures ( forall slot0, vp0 ::
                    && var hist_slot0 := get_or_default(hist, slot0, map[]);
                    && var hist_slot_vp0 := get_or_default(hist_slot0, vp0, {});
                    && var new_hist_slot0 := get_or_default(new_hist, slot0, map[]);
                    && var new_hist_slot_vp0 := get_or_default(new_hist_slot0, vp0, {});
                    && (( slot0 != id || vp0 != vp )
                        ==> 
                        hist_slot_vp0 == new_hist_slot_vp0
                        )
                    && ((slot0 == id && vp0 == vp )
                        ==> 
                        hist_slot_vp0 + {slashing_db_blocks} == new_hist_slot_vp0
                        )
            )
    {
        var hist_id := get_or_default(hist, id, map[]);
        var new_hist_id_vp := get_or_default(hist_id, vp, {}) + {slashing_db_blocks};
        hist[
            id := hist_id[
                vp := new_hist_id_vp
            ]
        ]
    }  


    function f_stop_block_consensus_instances(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        ids: set<Slot>
    ): ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }    
 
    function f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
        hist: map<Slot, map<BeaconBlock -> bool, set<set<SlashingDBBlock>>>>,
        new_active_consensus_instances : map<Slot, BlockConsensusValidityCheckState>,
        new_slashing_db_blocks: set<SlashingDBBlock>
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
                        var hist_k := get_or_default(hist, k, map[]);
                        var hist_k_vp := get_or_default(hist_k, vp, {}) + {new_slashing_db_blocks};
                        hist_k[
                            vp := hist_k_vp
                        ]
                    else
                        hist[k];
            ret
    }

    function f_update_block_consensus_instance_validity_check_states(
        m: map<Slot, BlockConsensusValidityCheckState>,
        new_slashing_db_blocks: set<SlashingDBBlock>
    ): (r: map<Slot, BlockConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    ensures (forall k: Slot | k in r.Keys
                ::
                &&  m[k].proposer_duty == r[k].proposer_duty
                && var vp := r[k].validityPredicate;
                && vp == (block: BeaconBlock) => ci_decision_is_valid_beacon_block(
                                                        new_slashing_db_blocks, 
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
                                                                    new_slashing_db_blocks, 
                                                                    block, 
                                                                    it.1.proposer_duty,
                                                                    it.1.randao_reveal 
                                                                 )
                )        
    } 

    function f_update_block_consensus_engine_state(
        s: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>,
        new_slashing_db_blocks: set<SlashingDBBlock>
    ): (r: ConsensusEngineState<BlockConsensusValidityCheckState, BeaconBlock, SlashingDBBlock>)
    ensures && var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_slashing_db_blocks
                );
            && s.slashing_db_hist.Keys + new_active_consensus_instances.Keys == r.slashing_db_hist.Keys
    {
        var new_active_consensus_instances := f_update_block_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_slashing_db_blocks
                );
        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := f_update_block_slashing_db_hist_with_new_consensus_instances_and_slashing_db_blocks(
                s.slashing_db_hist,
                new_active_consensus_instances,
                new_slashing_db_blocks
            )
        )
    }

    function f_initialize_att_consensus_engine_state(): ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    {
        ConsensusEngineState(
            active_consensus_instances := map[],
            slashing_db_hist := map[]
        )
    }

    function f_start_att_consensus_instance(
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
                validityPredicate := (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(attestation_slashing_db, ad, attestation_duty)
            );
        
        assert (acvc.validityPredicate == (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(attestation_slashing_db, ad, acvc.attestation_duty));
        
        var new_active_consensus_instances := 
            s.active_consensus_instances[
                id := acvc
            ];

        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := 
                f_update_att_slashing_db_hist_with_new_id_and_vp(
                    s.slashing_db_hist,
                    id,
                    acvc.validityPredicate,
                    attestation_slashing_db                    
                )
                
        )
    }

    function f_update_att_slashing_db_hist_with_new_id_and_vp(
        hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>,
        id: Slot,
        vp: AttestationData -> bool,
        attestation_slashing_db: set<SlashingDBAttestation>
    ): (new_hist: map<Slot, map<AttestationData -> bool, set<set<SlashingDBAttestation>>>>)
    ensures hist.Keys + { id } == new_hist.Keys
    ensures ( forall slot0, vp0 ::
                    && var hist_slot0 := get_or_default(hist, slot0, map[]);
                    && var hist_slot_vp0 := get_or_default(hist_slot0, vp0, {});
                    && var new_hist_slot0 := get_or_default(new_hist, slot0, map[]);
                    && var new_hist_slot_vp0 := get_or_default(new_hist_slot0, vp0, {});
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
        var hist_id := get_or_default(hist, id, map[]);
        var new_hist_id_vp := get_or_default(hist_id, vp, {}) + {attestation_slashing_db};
        hist[
            id := hist_id[
                vp := new_hist_id_vp
            ]
        ]
    }  

    function f_stop_att_consensus_instances(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        ids: set<Slot>
    ): ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>
    {
        s.(
            active_consensus_instances := s.active_consensus_instances - ids
        )
    }    

    function f_update_att_consensus_instance_validity_check_states(
        m: map<Slot, AttestationConsensusValidityCheckState>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: map<Slot, AttestationConsensusValidityCheckState>)
    ensures r.Keys <= m.Keys
    {
            map it | it in m.Items
                ::
                it.0 := it.1.(
                    validityPredicate := (ad: AttestationData) => ci_decision_att_signature_is_signed_with_pubkey_data(new_attestation_slashing_db, ad, it.1.attestation_duty)
                )        
    }
  
    function f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(
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
                        var hist_k := get_or_default(hist, k, map[]);
                        var hist_k_vp := get_or_default(hist_k, vp, {}) + {new_attestation_slashing_db};
                        hist_k[
                            vp := hist_k_vp
                        ]
                    else
                        hist[k];
            ret
    }

    function f_update_att_consensus_engine_state(
        s: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        new_attestation_slashing_db: set<SlashingDBAttestation>
    ): (r: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>)
    ensures && var new_active_consensus_instances := f_update_att_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );
            && s.slashing_db_hist.Keys + new_active_consensus_instances.Keys == r.slashing_db_hist.Keys
    {
        var new_active_consensus_instances := f_update_att_consensus_instance_validity_check_states(
                    s.active_consensus_instances,
                    new_attestation_slashing_db
                );
        s.(
            active_consensus_instances := new_active_consensus_instances,
            slashing_db_hist := f_update_att_slashing_db_hist_with_new_consensus_instances_and_slashing_db_attestations(
                s.slashing_db_hist,
                new_active_consensus_instances,
                new_attestation_slashing_db
            )
        )
    }

    
}