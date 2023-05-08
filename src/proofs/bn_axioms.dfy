include "../common/commons.dfy"

module Block_BN_Axioms
{
    import opened Types 
    import opened CommonFunctions

    datatype BNState = BNState(
        state_roots_of_imported_blocks: set<Root>,
        submitted_blocks: seq<SignedBeaconBlock>    
    )  

    function {:axiom} bn_get_fork_version(slot: Slot): Version

    function {:axiom} bn_get_validator_index(bnState: BNState, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} bn_get_epoch_committees(bnState: BNState, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks   
}

module Att_BN_Axioms
{
    import opened Types 
    import opened CommonFunctions

    datatype BNState = BNState(
        state_roots_of_imported_blocks: set<Root>,
        attestations_submitted: seq<Attestation>    
    )     

    function {:axiom} bn_get_fork_version(slot: Slot): Version

    function {:axiom} bn_get_validator_index(bnState: BNState, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} bn_get_epoch_committees(bnState: BNState, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks   
}