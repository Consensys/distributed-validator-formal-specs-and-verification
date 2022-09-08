include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"

module DVN_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions

    lemma dvn_init_inv52(dvn: DVState)       
    requires && var initial_attestation_slashing_db: set<SlashingDBAttestation> := {}; 
             && DV.Init(dvn, initial_attestation_slashing_db)        
    ensures inv52(dvn)
    {}    


    lemma dvn_next_event_inv52(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEvent(dvn, e, dvn')        
    requires inv52(dvn)
    ensures inv52(dvn')
    {}
    
    lemma dvn_next_inv52(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv52(dvn)
    ensures inv52(dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        dvn_next_event_inv52(dvn, e, dvn');
    }

    lemma dvn_init_inv42(dvn: DVState)       
    requires && var initial_attestation_slashing_db: set<SlashingDBAttestation> := {}; 
             && DV.Init(dvn, initial_attestation_slashing_db)    
    ensures inv42(dvn)
    {}  

    lemma dvn_next_event_inv42(dvn: DVState, e: DV.Event, dvn': DVState)       
    requires DV.NextEvent(dvn, e, dvn')        
    requires inv42(dvn)
    ensures inv42(dvn')
    {}

    lemma dvn_next_inv42(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv42(dvn)
    ensures inv42(dvn')
    {
        var e: DV.Event :| DV.NextEvent(dvn, e, dvn');
        dvn_next_event_inv42(dvn, e, dvn');
    }
    
}