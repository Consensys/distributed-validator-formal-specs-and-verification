include "../../../common/commons.dfy"
include "../../no_slashable_attestations/common/dvc_spec_axioms.dfy"
include "../../../proofs/no_slashable_attestations/common/attestation_creation_instrumented.dfy"
include "../../../specs/dvc/dvc_attestation_creation.dfy"

module Spec_Spec_NonInstr_Refinement
{
    import opened Types 
    import opened CommonFunctions
    import opened DVC_Externs
    import opened DVC_Spec_Axioms
    import DVC_Spec_NonInstr
    import DVC_Spec

    predicate consensusEngineStateRel(
        cei: DVC_Spec.ConsensusEngineState,
        ceni: DVC_Spec_NonInstr.ConsensusEngineState
    )
    {
        cei.attestation_consensus_active_instances == ceni.attestation_consensus_active_instances
    }

    predicate dVCNodeStateRel(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState
    )
    {
        && dvci.current_attestation_duty == dvcni.current_attestation_duty
        && dvci.latest_attestation_duty == dvcni.latest_attestation_duty
        && dvci.attestation_duties_queue == dvcni.attestation_duties_queue
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

    predicate dVCNodeStateAndOuputsRel(
        dvcandoi: DVC_Spec.DVCStateAndOuputs,
        dvcandoni: DVC_Spec_NonInstr.DVCStateAndOuputs        
    )
    {
        && dVCNodeStateRel(dvcandoi.state, dvcandoni.state)
        && dvcandoi.outputs == dvcandoni.outputs
    }

    lemma refine_f_serve_attestation_duty(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        attestation_duty: AttestationDuty
    )
    requires DVC_Spec.f_serve_attestation_duty.requires(dvci, attestation_duty)
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_serve_attestation_duty.requires(dvcni, attestation_duty)
    ensures dVCNodeStateAndOuputsRel(
        DVC_Spec.f_serve_attestation_duty(dvci, attestation_duty), 
        DVC_Spec_NonInstr.f_serve_attestation_duty(dvcni, attestation_duty)
    );    
    {
        var dvci := dvci.(
                attestation_duties_queue := dvci.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := dvci.all_rcvd_duties + {attestation_duty}
            );

        var dvcni := dvcni.(
                attestation_duties_queue := dvcni.attestation_duties_queue + [attestation_duty]
            );        

        refine_f_check_for_next_queued_duty(dvci, dvcni);                 
    }

    lemma refine_f_check_for_next_queued_duty(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState
    )
    requires DVC_Spec.f_check_for_next_queued_duty.requires(dvci)
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_check_for_next_queued_duty.requires(dvcni)
    ensures dVCNodeStateAndOuputsRel(
        DVC_Spec.f_check_for_next_queued_duty(dvci), 
        DVC_Spec_NonInstr.f_check_for_next_queued_duty(dvcni)
    );     
    decreases dvci.attestation_duties_queue
    {
        assert DVC_Spec_NonInstr.f_check_for_next_queued_duty.requires(dvcni);
        if  && dvci.attestation_duties_queue != [] 
            && (
                || dvci.attestation_duties_queue[0].slot in dvci.future_att_consensus_instances_already_decided
                || !dvci.current_attestation_duty.isPresent()
            )   
        {
            if dvci.attestation_duties_queue[0].slot in dvci.future_att_consensus_instances_already_decided.Keys
            {
                var queue_head := dvci.attestation_duties_queue[0];
                var new_attestation_slashing_db := DVC_Spec.f_update_attestation_slashing_db(dvci.attestation_slashing_db, dvci.future_att_consensus_instances_already_decided[queue_head.slot]);
                var dvci_new := dvci.(
                    attestation_duties_queue := dvci.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := dvci.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := DVC_Spec.updateConsensusInstanceValidityCheck(
                        dvci.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )
                );    

                assert          
                && dvcni.attestation_duties_queue != [] 
                && (
                    || dvcni.attestation_duties_queue[0].slot in dvcni.future_att_consensus_instances_already_decided
                    || !dvcni.current_attestation_duty.isPresent()
                );

                var dvcni_new := dvcni.(
                    attestation_duties_queue := dvcni.attestation_duties_queue[1..],
                    future_att_consensus_instances_already_decided := dvcni.future_att_consensus_instances_already_decided - {queue_head.slot},
                    attestation_slashing_db := new_attestation_slashing_db,
                    attestation_consensus_engine_state := DVC_Spec_NonInstr.updateConsensusInstanceValidityCheck(
                        dvcni.attestation_consensus_engine_state,
                        new_attestation_slashing_db
                    )
                ); 

                assert  dVCNodeStateRel(dvci_new, dvcni_new);   
                refine_f_check_for_next_queued_duty(dvci_new, dvcni_new);             
            }         
        } 
    }

    // lemma refine_f_listen_for_new_imported_blocks_precond(
    //     dvci: DVC_Spec.DVCState,
    //     dvcni: DVC_Spec_NonInstr.DVCState,
    //     block: BeaconBlock
    // )
    // requires DVC_Spec.f_listen_for_new_imported_blocks.requires(dvci, block)
    // requires dVCNodeStateRel(dvci, dvcni)    
    // {
    //     assert block.body.state_root in dvcni.bn.state_roots_of_imported_blocks;
    //     var valIndex := bn_get_validator_index(dvcni.bn, block.body.state_root, dvcni.dv_pubkey);
    //     forall a1, a2 | 
    //             && a1 in block.body.attestations
    //             && DVC_Spec_NonInstr.isMyAttestation(a1, dvcni, block, valIndex)
    //             && a2 in block.body.attestations
    //             && DVC_Spec_NonInstr.isMyAttestation(a2, dvcni, block, valIndex)                        
    //         // ::
    //         //     a1.data.slot == a2.data.slot ==> a1 == a2
    //     {
    //         assert bn_get_epoch_committees(dvci.bn, block.body.state_root, a1.data.index) == bn_get_epoch_committees(dvcni.bn, block.body.state_root, a1.data.index);
    //         assert valIndex == bn_get_validator_index(dvci.bn, block.body.state_root, dvci.dv_pubkey);
    //         assert DVC_Spec.isMyAttestation(a1, dvci, block, valIndex);
    //         // assert a1.data.slot == a2.data.slot ==> a1 == a2;
    //     }
    // // assert forall ad | ad in process.attestation_duties_queue :: ad.slot !in process.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys        
    // }

    // lemma l(
    //     s: seq<int>,
    //     i: int 
    // )
    // requires i in s
    // {
    //     var j :|  0 <= j < |s| && s[j] == i;
    //     var t :|  0 <= t < |s| && s[t] == i;
    //     assert j == t;
    // }

    lemma refine_f_att_consensus_decided(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        id: Slot,
        decided_attestation_data: AttestationData
    )
    requires DVC_Spec.f_att_consensus_decided.requires(dvci, id, decided_attestation_data)
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_att_consensus_decided.requires(dvcni, id, decided_attestation_data)
    ensures dVCNodeStateAndOuputsRel(
        DVC_Spec.f_att_consensus_decided(dvci, id, decided_attestation_data), 
        DVC_Spec_NonInstr.f_att_consensus_decided(dvcni, id, decided_attestation_data)
    );       
    {
        if  && dvci.current_attestation_duty.isPresent()
            && id == dvci.current_attestation_duty.safe_get().slot
        {
            var local_current_attestation_duty := dvci.current_attestation_duty.safe_get();

            var attestation_slashing_db := DVC_Spec.f_update_attestation_slashing_db(dvci.attestation_slashing_db, decided_attestation_data);

            var fork_version := bn_get_fork_version(compute_start_slot_at_epoch(decided_attestation_data.target.epoch));
            var attestation_signing_root := compute_attestation_signing_root(decided_attestation_data, fork_version);
            var attestation_signature_share := rs_sign_attestation(decided_attestation_data, fork_version, attestation_signing_root, dvci.rs);
            var attestation_with_signature_share := AttestationShare(
                    aggregation_bits := DVC_Spec.get_aggregation_bits(local_current_attestation_duty.validator_index),
                    data := decided_attestation_data, 
                    signature := attestation_signature_share
                ); 

            var dvci := 
                dvci.(
                    current_attestation_duty := None,
                    attestation_shares_to_broadcast := dvci.attestation_shares_to_broadcast[local_current_attestation_duty.slot := attestation_with_signature_share],
                    attestation_slashing_db := attestation_slashing_db,
                    attestation_consensus_engine_state := DVC_Spec.updateConsensusInstanceValidityCheck(
                        dvci.attestation_consensus_engine_state,
                        attestation_slashing_db
                    )
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

            assert dVCNodeStateRel(dvci, dvcni);      

            refine_f_check_for_next_queued_duty(dvci, dvcni);            
        }
    }

    lemma refine_f_listen_for_attestation_shares(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        attestation_share: AttestationShare
    )
    requires DVC_Spec.f_listen_for_attestation_shares.requires(dvci, attestation_share)
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_listen_for_attestation_shares.requires(dvcni, attestation_share)
    ensures dVCNodeStateAndOuputsRel(
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
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_listen_for_new_imported_blocks.requires(dvcni, block)
    ensures dVCNodeStateAndOuputsRel(
        DVC_Spec.f_listen_for_new_imported_blocks(dvci, block), 
        DVC_Spec_NonInstr.f_listen_for_new_imported_blocks(dvcni, block)
    );     
    {
        var new_consensus_instances_already_decided := DVC_Spec.f_listen_for_new_imported_blocks_helper_1(dvci, block);

        var att_consensus_instances_already_decided := dvci.future_att_consensus_instances_already_decided + new_consensus_instances_already_decided;

        var future_att_consensus_instances_already_decided := 
            DVC_Spec.f_listen_for_new_imported_blocks_helper_2(dvci, att_consensus_instances_already_decided);

        var dvci :=
                dvci.(
                    future_att_consensus_instances_already_decided := future_att_consensus_instances_already_decided,
                    attestation_consensus_engine_state := DVC_Spec.stopConsensusInstances(
                                    dvci.attestation_consensus_engine_state,
                                    att_consensus_instances_already_decided.Keys
                    ),
                    attestation_shares_to_broadcast := dvci.attestation_shares_to_broadcast - att_consensus_instances_already_decided.Keys,
                    rcvd_attestation_shares := dvci.rcvd_attestation_shares - att_consensus_instances_already_decided.Keys                    
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

        if dvci.current_attestation_duty.isPresent() && dvci.current_attestation_duty.safe_get().slot in att_consensus_instances_already_decided    
        {
            var decided_attestation_data := att_consensus_instances_already_decided[dvci.current_attestation_duty.safe_get().slot];
            var new_attestation_slashing_db := DVC_Spec.f_update_attestation_slashing_db(dvci.attestation_slashing_db, decided_attestation_data);
            var dvci := dvci.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := DVC_Spec.updateConsensusInstanceValidityCheck(
                    dvci.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );      

            var dvcni := dvcni.(
                current_attestation_duty := None,
                attestation_slashing_db := new_attestation_slashing_db,
                attestation_consensus_engine_state := DVC_Spec_NonInstr.updateConsensusInstanceValidityCheck(
                    dvcni.attestation_consensus_engine_state,
                    new_attestation_slashing_db
                )                
            );  

            assert dVCNodeStateRel(dvci, dvcni);    
            refine_f_check_for_next_queued_duty(dvci, dvcni);                    
        }
    }

    lemma refine_f_resend_attestation_share(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState
    )
    requires DVC_Spec.f_resend_attestation_share.requires(dvci)
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_resend_attestation_share.requires(dvcni)
    ensures dVCNodeStateAndOuputsRel(
        DVC_Spec.f_resend_attestation_share(dvci), 
        DVC_Spec_NonInstr.f_resend_attestation_share(dvcni)
    ); 
    {

    }

    lemma refine_f_process_event(
        dvci: DVC_Spec.DVCState,
        dvcni: DVC_Spec_NonInstr.DVCState,
        event: Event
    )
    requires DVC_Spec.f_process_event.requires(dvci, event)
    requires dVCNodeStateRel(dvci, dvcni)
    ensures DVC_Spec_NonInstr.f_process_event.requires(dvcni, event)
    ensures dVCNodeStateAndOuputsRel(
        DVC_Spec.f_process_event(dvci, event), 
        DVC_Spec_NonInstr.f_process_event(dvcni, event)
    ); 
    {
        match event 
            case ServeAttstationDuty(attestation_duty) => 
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
