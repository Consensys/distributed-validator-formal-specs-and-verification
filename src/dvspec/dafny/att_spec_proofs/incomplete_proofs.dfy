include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/fnc_inv.dfy"
include "../att_spec_proofs/dvn_next_invs_1_7.dfy"
include "../att_spec_proofs/dvn_next_invs_8_18.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"


module Incomplete_Proofs 
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas
    import opened DVN_Next_Invs_1_7
    import opened DVN_Next_Invs_8_18
    import opened Fnc_Inv    

    lemma {:axiom} axiom_inv19(dvc: DVCNodeState)    
    ensures inv19_body(dvc)

    

     
    
    

    

    lemma lemma_inv19_f_check_for_next_queued_duty(
        process: DVCNodeState,
        process': DVCNodeState
    )
    requires f_check_for_next_queued_duty.requires(process)
    requires process' == f_check_for_next_queued_duty(process).state        
    requires inv19_body(process)    
    // ensures inv19_body(process')
    decreases process.attestation_duties_queue
    {
        if  && process.attestation_duties_queue != [] 
            && (
                || process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided
                || !process.current_attestation_duty.isPresent()
            )    
        {            
                if process.attestation_duties_queue[0].slot in process.future_att_consensus_instances_already_decided.Keys 
                {
                    var queue_head := process.attestation_duties_queue[0];
                    var new_attestation_slashing_db := f_update_attestation_slashing_db(process.attestation_slashing_db, process.future_att_consensus_instances_already_decided[queue_head.slot]);
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..],
                        future_att_consensus_instances_already_decided := process.future_att_consensus_instances_already_decided - {queue_head.slot},
                        attestation_slashing_db := new_attestation_slashing_db,
                        attestation_consensus_engine_state := updateConsensusInstanceValidityCheck(
                            process.attestation_consensus_engine_state,
                            new_attestation_slashing_db
                        )                        
                    );
                    assert inv9_body(process_mod);
                    lemma_inv19_f_check_for_next_queued_duty(process_mod, process');
                }
                else
                { 
                    var next_duty := process.attestation_duties_queue[0];
                    var process_mod := process.(
                        attestation_duties_queue := process.attestation_duties_queue[1..]
                    );     

                    assert forall queued_duty: AttestationDuty | 
                                queued_duty in process_mod.attestation_duties_queue ::
                                    next_duty.slot <= queued_duty.slot;

                    assert inv19_body(process_mod);
                    lemma_inv19_f_start_next_duty(process_mod, next_duty, process');
                }
        }
        else
        {  }
    }

    lemma lemma_inv19_f_serve_attestation_duty(
        process: DVCNodeState,
        attestation_duty: AttestationDuty,
        process': DVCNodeState
    )  
    requires f_serve_attestation_duty.requires(process, attestation_duty)
    requires process' == f_serve_attestation_duty(process, attestation_duty).state
    requires inv19_body(process)
    ensures inv19_body(process')
    {
        var process_mod := process.(
                attestation_duties_queue := process.attestation_duties_queue + [attestation_duty],
                all_rcvd_duties := process.all_rcvd_duties + {attestation_duty}
            );  

        if process.latest_attestation_duty.isPresent() 
        {
            assert process_mod.latest_attestation_duty.isPresent();
            assert process.latest_attestation_duty.safe_get()
                        == process_mod.latest_attestation_duty.safe_get();
            assert process.latest_attestation_duty.safe_get().slot <= attestation_duty.slot;
            assert process_mod.latest_attestation_duty.safe_get().slot <= attestation_duty.slot;            
            assert inv19_body(process_mod);      
        }
        else 
        {
            assert !process_mod.latest_attestation_duty.isPresent();              
            assert inv19_body(process_mod);      
        }
        
        lemma_inv19_f_check_for_next_queued_duty(process_mod, process');        
    } 

    

     
     
       
}