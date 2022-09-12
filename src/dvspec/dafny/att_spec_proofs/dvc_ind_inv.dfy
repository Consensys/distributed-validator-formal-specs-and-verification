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

    lemma dvc_init_inv51(        
        dvn: DVState,
        hn: BLSPubkey,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        initial_attestation_slashing_db: set<SlashingDBAttestation>,
        rs_pubkey: BLSPubkey
    )
    requires && is_honest_node(dvn, hn)
             && var hn_state := dvn.honest_nodes_states[hn];
             && DVCNode_Spec.Init(hn_state, dv_pubkey, peers, construct_signed_attestation_signature, 
                    initial_attestation_slashing_db, rs_pubkey)
    ensures && var hn_state := dvn.honest_nodes_states[hn];
            && forall s: Slot :: inv51_body.requires(hn_state, s) ==> inv51_body(hn_state, s)
    {}    

    lemma dvc_init_inv5(        
        dvn: DVState,
        hn: BLSPubkey,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        initial_attestation_slashing_db: set<SlashingDBAttestation>,
        rs_pubkey: BLSPubkey
    )
    requires && is_honest_node(dvn, hn)
             && var hn_state := dvn.honest_nodes_states[hn];
             && DVCNode_Spec.Init(hn_state, dv_pubkey, peers, construct_signed_attestation_signature, 
                    initial_attestation_slashing_db, rs_pubkey)
    ensures && var hn_state := dvn.honest_nodes_states[hn];
            && inv5_body.requires(hn_state) ==> inv5_body(hn_state)
    {}  

    lemma f_start_next_duty_inv5_body(hn_state: DVCNodeState, hn_state': DVCNodeState, duty: AttestationDuty)
    requires && f_start_next_duty.requires(hn_state, duty)
             && f_start_next_duty(hn_state, duty).state == hn_state'         
    requires inv5_body(hn_state) 
    ensures inv5_body(hn_state')
    {}

    lemma {:axiom} assump_inv5_body(hn_state: DVCNodeState)
    ensures inv5_body(hn_state)

    // TODO
    /*
    lemma f_check_for_next_queued_duty_inv5_body(hn_state: DVCNodeState, hn_state': DVCNodeState)
    requires f_check_for_next_queued_duty.requires(hn_state)
    requires f_check_for_next_queued_duty(hn_state).state == hn_state'
    requires inv5_body(hn_state)
    // ensures inv5_body(hn_state')
    { 
        if  && hn_state.attestation_duties_queue != [] 
            && (
                || hn_state.attestation_duties_queue[0].slot in hn_state.future_att_consensus_instances_already_decided
                || !hn_state.current_attestation_duty.isPresent()
               )  
        {
            if hn_state.attestation_duties_queue[0].slot in hn_state.future_att_consensus_instances_already_decided.Keys 
            {
                assump_inv5_body(hn_state');    
            }
            else
            {                
                var duty: AttestationDuty :| && f_start_next_duty.requires(hn_state, duty)
                                             && f_start_next_duty(hn_state, duty).state == hn_state';
                f_start_next_duty_inv5_body(hn_state, hn_state', duty);
            }
        }
        else
        {
            assert f_check_for_next_queued_duty(hn_state).state == hn_state;
            assert hn_state == hn_state';
        }        
    }        
    */

    lemma dvc_next_inv5(        
        hn_state: DVCNodeState,
        hn_state': DVCNodeState
    )
    requires && ( exists e: Types.Event, output: Outputs :: DVCNode_Spec.Next(hn_state, e, hn_state', output) ) 
             && inv5_body(hn_state)
    ensures inv5_body(hn_state')
    {
        var e: Types.Event, outputs: Outputs :| DVCNode_Spec.Next(hn_state, e, hn_state', outputs);

        if e.ServeAttstationDuty? 
        { assump_inv5_body(hn_state'); }        
        else if e.AttConsensusDecided? 
        { 
            assump_inv5_body(hn_state'); 
        }
        else if e.ReceviedAttesttionShare?
        { 
            var share: AttestationShare :| f_listen_for_attestation_shares(hn_state, share).state == hn_state';
        }
        else if e.ImportedNewBlock?
        { 
            if ( exists block: BeaconBlock :: f_listen_for_new_imported_blocks.requires(hn_state, block) )
            {
                var block: BeaconBlock :| 
                    && f_listen_for_new_imported_blocks.requires(hn_state, block)
                    && f_listen_for_new_imported_blocks(hn_state, block).state == hn_state';
                assert f_listen_for_new_imported_blocks(hn_state, block).state == hn_state';
                assump_inv5_body(hn_state');             
            }
            else
            {}            
        }
        else if e.ResendAttestationShares?
        {             
            assert f_resend_attestation_share(hn_state).state == hn_state';
        }        
        else 
        {
            assert && e.NoEvent?
                   && inv5_body(hn_state');
        }
    } 

    lemma dvc_init_inv10(        
        dvn: DVState,
        hn: BLSPubkey,
        dv_pubkey: BLSPubkey,
        peers: set<BLSPubkey>,
        construct_signed_attestation_signature: (set<AttestationShare>) -> Optional<BLSSignature>,
        initial_attestation_slashing_db: set<SlashingDBAttestation>,
        rs_pubkey: BLSPubkey
    )
    requires && is_honest_node(dvn, hn)
             && var hn_state := dvn.honest_nodes_states[hn];
             && DVCNode_Spec.Init(hn_state, dv_pubkey, peers, construct_signed_attestation_signature, 
                    initial_attestation_slashing_db, rs_pubkey)
    ensures && var hn_state := dvn.honest_nodes_states[hn];
            && inv10_body(hn_state)
    {}  

    lemma dvc_next_inv10(        
        hn_state: DVCNodeState,
        hn_state': DVCNodeState
    )
    requires && ( exists e: Types.Event, output: Outputs :: DVCNode_Spec.Next(hn_state, e, hn_state', output) ) 
             && inv10_body(hn_state)
    ensures inv10_body(hn_state)
    {} 


/*    
    lemma dvc_next_inv51(hn_state: DVCNodeState, hn_state': DVCNodeState)       
    requires && ( forall s: Slot :: inv51_body.requires(hn_state, s) ==> inv51_body(hn_state, s) )
             && ( exists e: Types.Event, output: Outputs :: DVCNode_Spec.Next(hn_state, e, hn_state', output) )            
    ensures ( forall s: Slot :: inv51_body.requires(hn_state', s) ==> inv51_body(hn_state', s) )
    {}

    lemma dvn_next_inv2(dvn: DVState, dvn': DVState)       
    requires exists e: DV.Event :: DV.NextEvent(dvn, e, dvn')
    requires inv2(dvn)
    ensures inv2(dvn')
    {}
 */
    
}