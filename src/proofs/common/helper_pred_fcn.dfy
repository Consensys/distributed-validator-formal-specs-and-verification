include "../../common/commons.dfy"
include "../../specs/dvc/dvc_attestation_creation.dfy"
include "../../specs/consensus/consensus.dfy"
include "../../specs/network/network.dfy"
include "../../specs/dv/dv_attestation_creation.dfy"
include "../common/helper_sets_lemmas.dfy"
include "../no_slashable_attestations/common/attestation_creation_instrumented.dfy"
include "../no_slashable_attestations/supporting_lemmas/inv.dfy"

module Helper_Pred_Fcn
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVC_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Helper_Sets_Lemmas
    import opened DVC_Spec_Axioms
    import DVC_Spec_NonInstr
    
    predicate first_queued_att_duty_was_decided_or_ready_to_be_served(process: DVCState) 
    {
        && process.attestation_duties_queue != [] 
        &&  (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            ) 
    }

    predicate first_queued_att_duty_was_decided(process: DVCState)
    {
        process.attestation_duties_queue != [] 
        ==>
        process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys
    }

    function f_dequeue_attestation_duties_queue(process: DVCState)
        : (ret_process: DVCState)
    requires first_queued_att_duty_was_decided_or_ready_to_be_served(process)
    requires first_queued_att_duty_was_decided(process)
    ensures |ret_process.attestation_duties_queue| < |process.attestation_duties_queue|
    {
        var queue_head := process.attestation_duties_queue[0];
        var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
        var ret_process := 
            process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )
            );
        ret_process
    }
}