include "../common/commons.dfy"

module BN_Axioms
{
    import opened Types 
    

    datatype BNState<T(!new, ==)> = BNState(
        state_roots_of_imported_blocks: set<Root>,
        submitted_data: seq<T>    
    )  

    function {:axiom} bn_get_fork_version(slot: Slot): Version

    function {:axiom} bn_get_validator_index<T(!new, ==)> (bnState: BNState<T>, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} bn_get_epoch_committees<T(!new, ==)> (bnState: BNState<T>, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks   
}