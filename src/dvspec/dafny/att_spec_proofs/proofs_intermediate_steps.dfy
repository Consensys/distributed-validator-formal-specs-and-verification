include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"
include "../att_spec_proofs/helper_sets_lemmas.dfy"


module Proofs_Intermediate_Steps
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB    
    import opened Helper_Sets_Lemmas    
    


    

    lemma lemma_inv2_inv53(dvn: DVState)
    requires inv2(dvn)
    ensures inv53(dvn)
    { }
        
    lemma lemma_inv11_ind_inv(
        dvn: DVState
    )         
    requires inv1(dvn)      
    requires inv6(dvn)    
    requires inv14(dvn)
    ensures inv11(dvn)
    {   
        var queue := dvn.sequence_attestation_duties_to_be_served;
        var index := dvn.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dvn.honest_nodes_states.Keys 
        {
            var dvc := dvn.honest_nodes_states[hn];
            if dvc.current_attestation_duty.isPresent()
            {
                var duty := dvc.current_attestation_duty.safe_get();
                assert duty in dvc.all_rcvd_duties;  
                assert duty.slot <= next_duty.slot;  
            }
        }
    } 
    
    lemma lemma_inv12_ind_inv(
        dvn: DVState
    )         
    requires inv1(dvn)      
    requires inv7(dvn)    
    requires inv14(dvn)
    ensures inv12(dvn)
    {   
        var queue := dvn.sequence_attestation_duties_to_be_served;
        var index := dvn.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dvn.honest_nodes_states.Keys 
        {
            var dvc := dvn.honest_nodes_states[hn];
            if dvc.latest_attestation_duty.isPresent()
            {
                var duty := dvc.latest_attestation_duty.safe_get();
                assert duty in dvc.all_rcvd_duties;  
                assert duty.slot <= next_duty.slot;  
            }
        }
    } 
      
    lemma lemma_inv14_ind_inv(
        dvn: DVState
    )    
    requires inv1(dvn)  
    requires inv4(dvn)
    requires inv13(dvn)
    ensures inv14(dvn)    
    {   
        var queue := dvn.sequence_attestation_duties_to_be_served;
        var index := dvn.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dvn.honest_nodes_states.Keys 
        {
            var dvc := dvn.honest_nodes_states[hn];

            assert inv4_body(dvn, hn, dvc);


            forall rcvd_duty: AttestationDuty | rcvd_duty in dvc.all_rcvd_duties
            ensures rcvd_duty.slot <= next_duty.slot
            {
                
                var k: nat :| && 0 <= k < dvn.index_next_attestation_duty_to_be_served
                              && dvn.sequence_attestation_duties_to_be_served[k].node == hn
                              && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == rcvd_duty;

                assert dvn.sequence_attestation_duties_to_be_served[k].attestation_duty.slot <= next_duty.slot;

                assert rcvd_duty.slot <= next_duty.slot;
            }

            assert inv14_body(dvc, next_duty);
            
        }        
    }

    lemma lemma_inv15_ind_inv(
        dvn: DVState
    )    
    requires inv1(dvn)  
    requires inv4(dvn)
    requires inv5(dvn)
    requires inv13(dvn)
    requires inv14(dvn)
    ensures inv15(dvn)    
    {   
        var queue := dvn.sequence_attestation_duties_to_be_served;
        var index := dvn.index_next_attestation_duty_to_be_served;        
        var next_duty := queue[index].attestation_duty;
        var hn := queue[index].node;

        if hn in dvn.honest_nodes_states.Keys 
        {
            var dvc := dvn.honest_nodes_states[hn];

            assert inv4_body(dvn, hn, dvc);
            assert inv5_body(dvc);
            assert inv14_body(dvc, next_duty);


            forall queued_duty: AttestationDuty | queued_duty in dvc.attestation_duties_queue
            ensures queued_duty.slot <= next_duty.slot
            {
                assert queued_duty in dvc.all_rcvd_duties;
                
                var k: nat :| && 0 <= k < dvn.index_next_attestation_duty_to_be_served
                              && dvn.sequence_attestation_duties_to_be_served[k].node == hn
                              && dvn.sequence_attestation_duties_to_be_served[k].attestation_duty == queued_duty;

                assert dvn.sequence_attestation_duties_to_be_served[k].attestation_duty.slot <= next_duty.slot;

                assert queued_duty.slot <= next_duty.slot;
            }

            assert inv15_body(dvc, next_duty);
            
        }        
    }
    
}