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
    


    

    lemma lemma_inv53_ind_inv(dvn: DVState)
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

            assert inv4_body( hn, dvc.all_rcvd_duties, 
                              dvn.sequence_attestation_duties_to_be_served, 
                              dvn.index_next_attestation_duty_to_be_served);


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

            assert inv4_body(hn, dvc.all_rcvd_duties,
                             dvn.sequence_attestation_duties_to_be_served,
                             dvn.index_next_attestation_duty_to_be_served);
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


    lemma lemma_inv24_ind_inv(
        dvn: DVState
    )    
    requires inv18(dvn)
    requires inv22(dvn)
    requires inv23(dvn)
    ensures inv24(dvn)    
    {   
        forall hn: BLSPubkey | hn in dvn.honest_nodes_states.Keys
        {
            var dvc := dvn.honest_nodes_states[hn];

            if dvc.latest_attestation_duty.isPresent()
            {
                var latest_duty := dvc.latest_attestation_duty.safe_get();

                forall k: Slot, n: nat | 
                            && k in dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys 
                            && 0 <= n < |dvc.attestation_duties_queue|
                ensures k < dvc.attestation_duties_queue[n].slot;            
                {
                    calc {
                        k; 
                        <= 
                        latest_duty.slot;
                        <
                        dvc.attestation_duties_queue[n].slot;            
                    } 
                }

                assert inv24_body(dvc);
            }
            else
            {
                assert dvc.attestation_consensus_engine_state.attestation_consensus_active_instances.Keys == {};
                assert inv24_body(dvc);
            }
        }
    } 

    lemma lemma_inv51_ind_inv(
        dvn: DVState
    )    
    requires inv27(dvn)
    ensures inv51(dvn)    
    {  
        forall hn: BLSPubkey, s: Slot 
        ensures ( ( && is_honest_node(dvn, hn) 
                    && s in dvn.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
                  )
                  ==> inv51_body(dvn.honest_nodes_states[hn], s)
                )
        {
            if && is_honest_node(dvn, hn) 
               && s in dvn.honest_nodes_states[hn].attestation_consensus_engine_state.att_slashing_db_hist.Keys
            {
                var hn_state := dvn.honest_nodes_states[hn];
                assert inv27_body(hn_state);
                assert inv51_body(hn_state, s);
            }
            else
            {}
        }
            
    } 

    lemma lemma_inv50_ind_inv(
        dvn: DVState
    )    
    requires inv28(dvn)
    ensures inv50(dvn)    
    { 
        forall hn: BLSPubkey, s: Slot, vp: AttestationData -> bool | 
            && is_honest_node(dvn, hn)
            && var hn_state := dvn.honest_nodes_states[hn];
            && s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys
            && vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s]            
        ensures ( exists duty, db ::
                    && var hn_state := dvn.honest_nodes_states[hn];
                    && inv50_body(dvn, hn, s, db, duty, vp) 
                )                
        {
            var hn_state := dvn.honest_nodes_states[hn];            
            assert inv28_body(hn_state);
            assert s in hn_state.attestation_consensus_engine_state.att_slashing_db_hist.Keys;
            assert vp in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s];

            assert ( exists db: set<SlashingDBAttestation>, duty: AttestationDuty ::
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                    );

            var db: set<SlashingDBAttestation>, duty: AttestationDuty :|
                        && duty.slot == s
                        && db in hn_state.attestation_consensus_engine_state.att_slashing_db_hist[s][vp]
                        && vp == (ad: AttestationData) => consensus_is_valid_attestation_data(db, ad, duty)
                    ;

            assert inv50_body(dvn, hn, s, db, duty, vp);
        }
    }    
}