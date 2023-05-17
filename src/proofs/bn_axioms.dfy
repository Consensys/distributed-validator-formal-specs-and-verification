include "../common/commons.dfy"

module BN_Axioms
{
    import opened Types 
    
    function {:axiom} af_bn_get_fork_version(slot: Slot): Version

    function {:axiom} af_bn_get_validator_index<T(!new, ==)> (bnState: BNState<T>, state_id: Root, validator_id: BLSPubkey): (vi: Optional<ValidatorIndex>)
    requires state_id in bnState.state_roots_of_imported_blocks

    function {:axiom} af_bn_get_epoch_committees<T(!new, ==)> (bnState: BNState<T>, state_id: Root, index: CommitteeIndex): (sv: seq<ValidatorIndex>) 
    requires state_id in bnState.state_roots_of_imported_blocks   
}