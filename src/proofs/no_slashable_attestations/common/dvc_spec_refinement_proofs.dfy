include "../../../common/commons.dfy"
include "../../../proofs/rs_axioms.dfy"
include "../../../proofs/no_slashable_attestations/common/dvc_attestation_creation_instrumented.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"
include "../../common/att_helper_pred_fcn.dfy"

module Spec_Spec_Non_Instr_Refinement
{
    import opened Types 
    import opened Common_Functions
    import opened Set_Seq_Helper
    import opened Signing_Methods
    import opened BN_Axioms
    import opened RS_Axioms
    import Non_Instr_Att_DVC
    import Att_DVC
    import opened Att_Helper_Pred_Fcn
    import Non_Instr_Consensus_Engine
    import Consensus_Engine

    predicate consensusEngineStateRel(
        cei: ConsensusEngineState<AttestationConsensusValidityCheckState, AttestationData, SlashingDBAttestation>,
        ceni: NonInstrConsensusEngineState<AttestationConsensusValidityCheckState>
    )
    {
        cei.active_consensus_instances == ceni.active_consensus_instances
    }

    predicate AttDVCStateRel(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState
    )
    {
        && dvci.current_attestation_duty == dvcni.current_attestation_duty
        && dvci.latest_attestation_duty == dvcni.latest_attestation_duty
        && dvci.attestation_slashing_db == dvcni.attestation_slashing_db
        && dvci.rcvd_attestation_shares == dvcni.rcvd_attestation_shares
        && dvci.attestation_shares_to_broadcast == dvcni.attestation_shares_to_broadcast
        && consensusEngineStateRel(dvci.attestation_consensus_engine_state, dvcni.attestation_consensus_engine_state)
        && dvci.peers == dvcni.peers
        && dvci.construct_signed_attestation_signature == dvcni.construct_signed_attestation_signature
        && dvci.dv_pubkey == dvcni.dv_pubkey
        && dvci.future_att_consensus_instances_already_decided == dvcni.future_att_consensus_instances_already_decided
        && dvci.bn == dvcni.bn
        && dvci.rs == dvcni.rs
    }

    predicate AttDVCStateAndOuputsRel(
        dvcandoi: DVCStateAndOuputs<AttDVCState, AttestationOutputs>,
        dvcandoni: DVCStateAndOuputs<NonInstrAttDVCState, AttestationOutputs>      
    )
    {
        && AttDVCStateRel(dvcandoi.state, dvcandoni.state)
        && dvcandoi.outputs == dvcandoni.outputs
    }

    lemma lem_refine_f_serve_attestation_duty(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState,
        attestation_duty: AttestationDuty
    )
    requires Att_DVC.f_serve_attestation_duty.requires(dvci, attestation_duty)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_serve_attestation_duty.requires(dvcni, attestation_duty)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_serve_attestation_duty(dvci, attestation_duty), 
        Non_Instr_Att_DVC.f_serve_attestation_duty(dvcni, attestation_duty)
    );    
    {
        var dvci_after_stopping_active_consensus_instance := Att_DVC.f_terminate_current_attestation_duty(dvci);
        var dvci_new := Att_DVC.f_check_for_next_duty(
                                dvci_after_stopping_active_consensus_instance,
                                attestation_duty
                            );

        var dvcni_after_stopping_active_consensus_instance := Non_Instr_Att_DVC.f_terminate_current_attestation_duty(dvcni);
        var dvcni_new := Non_Instr_Att_DVC.f_check_for_next_duty(
                                dvcni_after_stopping_active_consensus_instance,
                                attestation_duty
                            );               
    }

    lemma lem_refine_f_terminate_current_attestation_duty(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState
    )
    requires Att_DVC.f_terminate_current_attestation_duty.requires(dvci)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_terminate_current_attestation_duty.requires(dvcni)
    ensures AttDVCStateRel(
        Att_DVC.f_terminate_current_attestation_duty(dvci), 
        Non_Instr_Att_DVC.f_terminate_current_attestation_duty(dvcni)
    ); 
    {
        if dvci.current_attestation_duty.isPresent()
        {
            var dvci_new :=
                    dvci.(
                        current_attestation_duty := None,
                        attestation_consensus_engine_state := Consensus_Engine.f_stop_att_consensus_instances(
                                        dvci.attestation_consensus_engine_state,
                                        {dvci.current_attestation_duty.safe_get().slot}
                        )               
                    );                    
            
            assert dvcni.current_attestation_duty.isPresent();

            var dvcni_new :=
                    dvcni.(
                        current_attestation_duty := None,
                        attestation_consensus_engine_state := Non_Instr_Consensus_Engine.f_stop_att_consensus_instances(
                                        dvcni.attestation_consensus_engine_state,
                                        {dvcni.current_attestation_duty.safe_get().slot}
                        )               
                    );

            assert  AttDVCStateRel(dvci_new, dvcni_new); 
        }
    }  

    lemma lem_refine_f_check_for_next_duty(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState,
        attestation_duty: AttestationDuty
    )
    requires Att_DVC.f_check_for_next_duty.requires(dvci, attestation_duty)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_check_for_next_duty.requires(dvcni, attestation_duty)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_check_for_next_duty(dvci, attestation_duty), 
        Non_Instr_Att_DVC.f_check_for_next_duty(dvcni, attestation_duty)
    )    
    {
        assert Att_DVC.f_check_for_next_duty.requires(dvci, attestation_duty);
        assert Non_Instr_Att_DVC.f_check_for_next_duty.requires(dvcni, attestation_duty);
        
        if attestation_duty.slot in dvci.future_att_consensus_instances_already_decided.Keys
        {
            var new_attestation_slashing_db := 
                    Att_DVC.f_update_attestation_slashing_db(
                        dvci.attestation_slashing_db, 
                        dvci.future_att_consensus_instances_already_decided[attestation_duty.slot]
                    );
            var dvci_new := 
                    dvci.(
                        future_att_consensus_instances_already_decided := dvci.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := Consensus_Engine.f_update_att_consensus_engine_state(
                            dvci.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );

            assert attestation_duty.slot in dvcni.future_att_consensus_instances_already_decided.Keys;

            var dvcni_new := dvcni.(
                future_att_consensus_instances_already_decided := dvcni.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := Non_Instr_Consensus_Engine.f_update_att_consensus_engine_state(
                    dvcni.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )
            ); 

            assert  AttDVCStateRel(dvci_new, dvcni_new);   
        }         
    }

    lemma lem_refine_f_att_consensus_decided(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    )
    requires Att_DVC.f_att_consensus_decided.requires(dvci, id, decided_attestation_data)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_att_consensus_decided.requires(dvcni, id, decided_attestation_data)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_att_consensus_decided(dvci, id, decided_attestation_data), 
        Non_Instr_Att_DVC.f_att_consensus_decided(dvcni, id, decided_attestation_data)
    );       
    {
        if  is_decided_data_for_current_slot(dvci, decided_attestation_data, id)
        {
            var local_current_attestation_duty := dvci.current_attestation_duty.safe_get();

            var attestation_slashing_db := Att_DVC.f_update_attestation_slashing_db(dvci.attestation_slashing_db, decided_attestation_data);

            var fork_version := af_bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := af_rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, dvci.rs);
            

            var dvci := f_update_process_after_att_duty_decided(
                                    dvci,
                                    id,
                                    decided_attestation_data
                                );


            assert dvcni.current_attestation_duty.safe_get().slot == id;


            var attestation_slashing_db_dvcni := Non_Instr_Att_DVC.f_update_attestation_slashing_db(dvcni.attestation_slashing_db, decided_attestation_data);

            var attestation_with_signature_share_dvcni := AttestationShare(
                    aggregation_bits := Non_Instr_Att_DVC.f_get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                );                    

            var dvcni := 
                dvcni.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := dvcni.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share_dvcni],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := Non_Instr_Consensus_Engine.f_update_att_consensus_engine_state(
                        dvcni.attestation_consensus_engine_state,
                        attestation_slashing_db
                    )
                );     

            assert AttDVCStateRel(dvci, dvcni);      
        }
    }

    lemma lem_refine_f_listen_for_attestation_shares(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState,
        attestation_share: AttestationShare
    )
    requires Att_DVC.f_listen_for_attestation_shares.requires(dvci, attestation_share)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_listen_for_attestation_shares.requires(dvcni, attestation_share)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_listen_for_attestation_shares(dvci, attestation_share), 
        Non_Instr_Att_DVC.f_listen_for_attestation_shares(dvcni, attestation_share)
    );    
    {

    }     

    lemma lem_refine_f_listen_for_new_imported_blocks(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState,
        block: BeaconBlock
    )
    requires Att_DVC.f_listen_for_new_imported_blocks.requires(dvci, block)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_listen_for_new_imported_blocks.requires(dvcni, block)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_listen_for_new_imported_blocks(dvci, block), 
        Non_Instr_Att_DVC.f_listen_for_new_imported_blocks(dvcni, block)
    );     
    {
        var new_consensus_instances_already_decided := Att_DVC.f_listen_for_new_imported_blocks_helper_1(dvci, block);

        var att_consensus_instances_already_decided := dvci.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            Att_DVC.f_listen_for_new_imported_blocks_helper_2(dvci, att_consensus_instances_already_decided);

        var dvci := f_f_stop_att_consensus_instances_after_receiving_new_imported_blocks(
                                dvci,
                                block
                            );

        assert Non_Instr_Att_DVC.f_listen_for_new_imported_blocks.requires(dvcni, block); 

        var new_consensus_instances_already_decided_dvcni := Non_Instr_Att_DVC.f_listen_for_new_imported_blocks_helper_1(dvcni, block);

        var att_consensus_instances_already_decided_dvcni := dvcni.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided_dvcni;

        var future_att_consensus_instances_already_decided_dvcni := 
            Non_Instr_Att_DVC.f_listen_for_new_imported_blocks_helper_2(dvcni, att_consensus_instances_already_decided_dvcni);                

        var dvcni :=
                dvcni.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided_dvcni,
                    attestation_consensus_engine_state := Non_Instr_Consensus_Engine.f_stop_att_consensus_instances(
                                    dvcni.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := dvcni.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := dvcni.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
                );              
        assert new_consensus_instances_already_decided_dvcni == new_consensus_instances_already_decided;  

        assert att_consensus_instances_already_decided_dvcni == att_consensus_instances_already_decided;

        assert future_att_consensus_instances_already_decided_dvcni == future_att_consensus_instances_already_decided;

        if pred_listen_for_new_imported_blocks_checker(
                        dvci,
                        att_consensus_instances_already_decided
                    )
        {
            var decided_attestation_data := att_consensus_instances_already_decided[dvci.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := Att_DVC.f_update_attestation_slashing_db(dvci.attestation_slashing_db, decided_attestation_data);
            var dvci := f_f_update_att_consensus_engine_state_in_listen_for_new_imported_blocks(
                                    dvci,
                                    att_consensus_instances_already_decided
                                );

            var dvcni := dvcni.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := Non_Instr_Consensus_Engine.f_update_att_consensus_engine_state(
                    dvcni.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );  

            assert AttDVCStateRel(dvci, dvcni);    
        }
    }

    lemma lem_refine_f_resend_attestation_shares(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState
    )
    requires Att_DVC.f_resend_attestation_shares.requires(dvci)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_resend_attestation_shares.requires(dvcni)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_resend_attestation_shares(dvci), 
        Non_Instr_Att_DVC.f_resend_attestation_shares(dvcni)
    ); 
    {
        
    }

    lemma lem_refine_f_process_event(
        dvci: AttDVCState,
        dvcni: NonInstrAttDVCState,
        event: AttestationEvent
    )
    requires Att_DVC.f_process_event.requires(dvci, event)
    requires AttDVCStateRel(dvci, dvcni)
    ensures Non_Instr_Att_DVC.f_process_event.requires(dvcni, event)
    ensures AttDVCStateAndOuputsRel(
        Att_DVC.f_process_event(dvci, event), 
        Non_Instr_Att_DVC.f_process_event(dvcni, event)
    ); 
    {
        match event 
            case ServeAttestationDuty(attestation_duty) => 
                lem_refine_f_serve_attestation_duty(dvci, dvcni, attestation_duty);
            case AttConsensusDecided(id, decided_attestation_data) => 
                lem_refine_f_att_consensus_decided(dvci, dvcni, id,  decided_attestation_data);
            case ReceivedAttestationShare(attestation_share) => 
                lem_refine_f_listen_for_attestation_shares(dvci, dvcni, attestation_share);
            case ImportedNewBlock(block) => 
                lem_refine_f_listen_for_new_imported_blocks(dvci, dvcni, block);
            case ResendAttestationShares => 
                lem_refine_f_resend_attestation_shares(dvci, dvcni);
            case NoEvent => 
    }    
}
