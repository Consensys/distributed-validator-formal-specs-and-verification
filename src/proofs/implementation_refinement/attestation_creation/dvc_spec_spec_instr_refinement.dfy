include "../../../common/commons.dfy"
include "../../no_slashable_attestations/common/dvc_spec_axioms.dfy"
include "../../../proofs/no_slashable_attestations/common/attestation_creation_instrumented.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"
include "../../common/helper_pred_fcn.dfy"

module Spec_Spec_NonInstr_Refinement
{
    import opened Types 
    import opened CommonFunctions
    import opened DVC_Spec_Axioms
    import DVC_Spec_NonInstr
    import DVC_Spec
    import opened Helper_Pred_Fcn

    predicate consensusEngineStateRel(
        cei: DVC_Spec.ConsensusEngineState,
        ceni: DVC_Spec_NonInstr.ConsensusEngineState
    )
    {
        cei.active_attestation_consensus_instances == ceni.active_attestation_consensus_instances
    }

    predicate DVCStateRel(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState
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

    predicate DVCStateAndOuputsRel(
        dvcandoi: DVC_Spec.DVCStateAndOuputs,
        dvcandoni: DVC_Spec_NonInstr.DVCStateAndOuputs        
    )
    {
        && DVCStateRel(dvcandoi.state, dvcandoni.state)
        && dvcandoi.outputs == dvcandoni.outputs
    }

    lemma refine_f_serve_attestation_duty(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        attestation_duty: AttestationDuty
    )
    requires DVC_Spec.f_serve_attestation_duty.requires(dvci, attestation_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_serve_attestation_duty.requires(dvcni, attestation_duty)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_serve_attestation_duty(dvci, attestation_duty), 
        DVC_Spec_NonInstr.f_serve_attestation_duty(dvcni, attestation_duty)
    );    
    {
        var dvci_after_stopping_active_consensus_instance := DVC_Spec.f_terminate_current_attestation_duty(dvci);
        var dvci_new := DVC_Spec.f_check_for_next_duty(
                                dvci_after_stopping_active_consensus_instance,
                                attestation_duty
                            );

        var dvcni_after_stopping_active_consensus_instance := DVC_Spec_NonInstr.f_terminate_current_attestation_duty(dvcni);
        var dvcni_new := DVC_Spec_NonInstr.f_check_for_next_duty(
                                dvcni_after_stopping_active_consensus_instance,
                                attestation_duty
                            );               
    }

    lemma refine_f_terminate_current_attestation_duty(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState
    )
    requires DVC_Spec.f_terminate_current_attestation_duty.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_terminate_current_attestation_duty.requires(dvcni)
    ensures DVCStateRel(
        DVC_Spec.f_terminate_current_attestation_duty(dvci), 
        DVC_Spec_NonInstr.f_terminate_current_attestation_duty(dvcni)
    ); 
    {
        if dvci.current_attestation_duty.isPresent()
        {
            var dvci_new :=
                    dvci.(
                        current_attestation_duty := None,
                        attestation_consensus_engine_state := DVC_Spec.stopConsensusInstances(
                                        dvci.attestation_consensus_engine_state,
                                        {dvci.current_attestation_duty.safe_get().slot}
                        )               
                    );                    
            
            assert dvcni.current_attestation_duty.isPresent();

            var dvcni_new :=
                    dvcni.(
                        current_attestation_duty := None,
                        attestation_consensus_engine_state := DVC_Spec_NonInstr.stopConsensusInstances(
                                        dvcni.attestation_consensus_engine_state,
                                        {dvcni.current_attestation_duty.safe_get().slot}
                        )               
                    );

            assert  DVCStateRel(dvci_new, dvcni_new); 
        }
    }  

    lemma refine_f_check_for_next_duty(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        attestation_duty: AttestationDuty
    )
    requires DVC_Spec.f_check_for_next_duty.requires(dvci, attestation_duty)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_check_for_next_duty.requires(dvcni, attestation_duty)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_check_for_next_duty(dvci, attestation_duty), 
        DVC_Spec_NonInstr.f_check_for_next_duty(dvcni, attestation_duty)
    )    
    {
        assert DVC_Spec.f_check_for_next_duty.requires(dvci, attestation_duty);
        assert DVC_Spec_NonInstr.f_check_for_next_duty.requires(dvcni, attestation_duty);
        
        if attestation_duty.slot in dvci.future_att_consensus_instances_already_decided.Keys
        {
            var new_attestation_slashing_db := 
                    DVC_Spec.f_update_attestation_slashing_db(
                        dvci.attestation_slashing_db, 
                        dvci.future_att_consensus_instances_already_decided[attestation_duty.slot]
                    );
            var dvci_new := 
                    dvci.(
                        future_att_consensus_instances_already_decided := dvci.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := DVC_Spec.updateConsensusInstanceValidityCheck(
                            dvci.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );

            assert attestation_duty.slot in dvcni.future_att_consensus_instances_already_decided.Keys;

            var dvcni_new := dvcni.(
                future_att_consensus_instances_already_decided := dvcni.future_att_consensus_instances_already_decided - {attestation_duty.slot},
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := DVC_Spec_NonInstr.updateConsensusInstanceValidityCheck(
                    dvcni.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )
            ); 

            assert  DVCStateRel(dvci_new, dvcni_new);   
        }         
    }

    lemma refine_f_att_consensus_decided(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    )
    requires DVC_Spec.f_att_consensus_decided.requires(dvci, id, decided_attestation_data)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_att_consensus_decided.requires(dvcni, id, decided_attestation_data)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_att_consensus_decided(dvci, id, decided_attestation_data), 
        DVC_Spec_NonInstr.f_att_consensus_decided(dvcni, id, decided_attestation_data)
    );       
    {
        if  is_decided_data_for_current_slot(dvci, decided_attestation_data, id)
        {
            var local_current_attestation_duty := dvci.current_attestation_duty.safe_get();

            var attestation_slashing_db := DVC_Spec.f_update_attestation_slashing_db(dvci.attestation_slashing_db, decided_attestation_data);

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, dvci.rs);
            

            var dvci := f_update_process_after_att_duty_decided(
                                    dvci,
                                    id,
                                    decided_attestation_data
                                );


            assert dvcni.current_attestation_duty.safe_get().slot == id;


            var attestation_slashing_db_dvcni := DVC_Spec_NonInstr.f_update_attestation_slashing_db(dvcni.attestation_slashing_db, decided_attestation_data);

            var attestation_with_signature_share_dvcni := AttestationShare(
                    aggregation_bits := DVC_Spec_NonInstr.get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                );                    

            var dvcni := 
                dvcni.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := dvcni.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share_dvcni],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := DVC_Spec_NonInstr.updateConsensusInstanceValidityCheck(
                        dvcni.attestation_consensus_engine_state,
                        attestation_slashing_db
                    )
                );     

            assert DVCStateRel(dvci, dvcni);      
        }
    }

    lemma refine_f_listen_for_attestation_shares(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        attestation_share: AttestationShare
    )
    requires DVC_Spec.f_listen_for_attestation_shares.requires(dvci, attestation_share)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_listen_for_attestation_shares.requires(dvcni, attestation_share)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_listen_for_attestation_shares(dvci, attestation_share), 
        DVC_Spec_NonInstr.f_listen_for_attestation_shares(dvcni, attestation_share)
    );    
    {

    }     

    lemma refine_f_listen_for_new_imported_blocks(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        block: BeaconBlock
    )
    requires DVC_Spec.f_listen_for_new_imported_blocks.requires(dvci, block)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_listen_for_new_imported_blocks.requires(dvcni, block)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_listen_for_new_imported_blocks(dvci, block), 
        DVC_Spec_NonInstr.f_listen_for_new_imported_blocks(dvcni, block)
    );     
    {
        var new_consensus_instances_already_decided := DVC_Spec.f_listen_for_new_imported_blocks_helper_1(dvci, block);

        var att_consensus_instances_already_decided := dvci.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            DVC_Spec.f_listen_for_new_imported_blocks_helper_2(dvci, att_consensus_instances_already_decided);

        var dvci := f_stopConsensusInstances_after_receiving_new_imported_blocks(
                                dvci,
                                block
                            );

        assert DVC_Spec_NonInstr.f_listen_for_new_imported_blocks.requires(dvcni, block); 

        var new_consensus_instances_already_decided_dvcni := DVC_Spec_NonInstr.f_listen_for_new_imported_blocks_helper_1(dvcni, block);

        var att_consensus_instances_already_decided_dvcni := dvcni.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided_dvcni;

        var future_att_consensus_instances_already_decided_dvcni := 
            DVC_Spec_NonInstr.f_listen_for_new_imported_blocks_helper_2(dvcni, att_consensus_instances_already_decided_dvcni);                

        var dvcni :=
                dvcni.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided_dvcni,
                    attestation_consensus_engine_state := DVC_Spec_NonInstr.stopConsensusInstances(
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
            var new_attestation_slashing_db := DVC_Spec.f_update_attestation_slashing_db(dvci.attestation_slashing_db, decided_attestation_data);
            var dvci := f_updateConsensusInstanceValidityCheck_in_listen_for_new_imported_blocks(
                                    dvci,
                                    att_consensus_instances_already_decided
                                );

            var dvcni := dvcni.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := DVC_Spec_NonInstr.updateConsensusInstanceValidityCheck(
                    dvcni.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );  

            assert DVCStateRel(dvci, dvcni);    
        }
    }

    lemma refine_f_resend_attestation_share(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState
    )
    requires DVC_Spec.f_resend_attestation_share.requires(dvci)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_resend_attestation_share.requires(dvcni)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_resend_attestation_share(dvci), 
        DVC_Spec_NonInstr.f_resend_attestation_share(dvcni)
    ); 
    {
        
    }

    lemma refine_f_process_event(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        event: AttestationEvent
    )
    requires DVC_Spec.f_process_event.requires(dvci, event)
    requires DVCStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_process_event.requires(dvcni, event)
    ensures DVCStateAndOuputsRel(
        DVC_Spec.f_process_event(dvci, event), 
        DVC_Spec_NonInstr.f_process_event(dvcni, event)
    ); 
    {
        match event 
            case ServeAttestationDuty(attestation_duty) => 
                refine_f_serve_attestation_duty(dvci, dvcni, attestation_duty);
            case AttConsensusDecided(id, decided_attestation_data) => 
                refine_f_att_consensus_decided(dvci, dvcni, id,  decided_attestation_data);
            case ReceivedAttestationShare(attestation_share) => 
                refine_f_listen_for_attestation_shares(dvci, dvcni, attestation_share);
            case ImportedNewBlock(block) => 
                refine_f_listen_for_new_imported_blocks(dvci, dvcni, block);
            case ResendAttestationShares => 
                refine_f_resend_attestation_share(dvci, dvcni);
            case NoEvent => 
    }    
}
