include "../commons.dfy"
include "../specification/dvc_spec.dfy"
include "../specification/consensus.dfy"
include "../specification/network.dfy"
include "../specification/dvn.dfy"
include "../att_spec_proofs/inv.dfy"
include "../att_spec_proofs/assump.dfy"

module DVN_Init_Ind_Inv
{
    import opened Types 
    import opened CommonFunctions
    import opened ConsensusSpec
    import opened NetworkSpec
    import opened DVCNode_Spec
    import opened DV
    import opened Att_Inv_With_Empty_Initial_Attestation_Slashing_DB
    import opened Att_Assumptions

    
    lemma dvn_init_inv5(dvn: DVState)
    requires && var initial_attestation_slashing_db: set<SlashingDBAttestation> := {}; 
             && DV.Init(dvn, initial_attestation_slashing_db)    
    ensures inv5(dvn)
    {}

    lemma dvn_init_inv10(dvn: DVState)
    requires && var initial_attestation_slashing_db: set<SlashingDBAttestation> := {}; 
             && DV.Init(dvn, initial_attestation_slashing_db)    
    ensures inv5(dvn)
    {}

    lemma dvn_init_inv42(dvn: DVState)       
    requires && var initial_attestation_slashing_db: set<SlashingDBAttestation> := {}; 
             && DV.Init(dvn, initial_attestation_slashing_db)    
    ensures inv42(dvn)
    {}  

    lemma dvn_init_inv52(dvn: DVState)       
    requires && var initial_attestation_slashing_db: set<SlashingDBAttestation> := {}; 
             && DV.Init(dvn, initial_attestation_slashing_db)        
    ensures inv52(dvn)
    {}    

    lemma prop52_a(dvn: DVState, hn: BLSPubkey)       
    requires inv52(dvn)    
    requires hn in dvn.honest_nodes_states.Keys
    ensures hn in dvn.all_nodes
    ensures hn !in dvn.adversary.nodes
    {
        calc {
            hn in dvn.adversary.nodes;
            ==> 
            hn in dvn.adversary.nodes && hn in dvn.honest_nodes_states.Keys;
            ==>
            hn in dvn.honest_nodes_states.Keys * dvn.adversary.nodes;
            ==> 
            false;
        }        
    }

}