include "../commons.dfy"

// Note: Only safety properties are expressed at the moment.
module ConsensusSpec
{
    import opened Types 
    import opened CommonFunctions

    datatype InCommand<!D> = 
    | Start(node: BLSPubkey)
    | Stop(node: BLSPubkey)

    datatype OutCommand<D> = 
    | Decided(node: BLSPubkey, value: D)

    datatype HonestNodeStatus = NOT_DECIDED | DECIDED

    datatype ConsensusInstance<!D(!new, 0)> = ConsensusInstance(
        all_nodes: set<BLSPubkey>,
        decided_value: Optional<D>,
        honest_nodes_status: map<BLSPubkey, HonestNodeStatus>,
        ghost honest_nodes_validity_functions: map<BLSPubkey, set<D -> bool>>
        // ghost honest_nodes: set<BLSPubkey>
    )    


    function f(n:nat): nat
    {
        if n > 0 then
            (n-1)/3
        else
            0
    }

    function quorum(n:nat):nat
    {
        if n > 0 then
            (2*n -1)/3 + 1 
        else 
            0
    }

    lemma test_quorum(n: nat)
    ensures quorum(n) * 3 >= 2 * n
    { }

    predicate ByzThresholdAssumption(
        all_nodes: set<BLSPubkey>,
        honest_nodes: set<BLSPubkey>,
        dishonest_nodes: set<BLSPubkey>
    )
    {        
        && 2 * |dishonest_nodes| + 1 <= |honest_nodes|
        && all_nodes == honest_nodes + dishonest_nodes
        && honest_nodes * dishonest_nodes == {}
    }


    predicate isConditionForSafetyTrue<D(!new, 0)>(
        s: ConsensusInstance
    )
    {
        quorum(|s.all_nodes|) <= |s.honest_nodes_status|
    }

    predicate Init<D(!new, 0)>(
        s: ConsensusInstance, 
        all_nodes: set<BLSPubkey>, 
        honest_nodes: set<BLSPubkey>)
    {
        && s.all_nodes == all_nodes
        && !s.decided_value.isPresent()
        && s.honest_nodes_status.Keys == honest_nodes
        && s.honest_nodes_validity_functions == map[]
        && (forall t | t in s.honest_nodes_status.Values :: t == NOT_DECIDED)
    }

    predicate Next<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    {
        exists s'': ConsensusInstance ::
            // First we let the consensus protocol and the various nodes possibly decide on a value
            && NextConsensusDecides(s, honest_nodes_validity_predicates, s'')
            // Then we let the node take an input/output step
            && NextNodeStep(s'', honest_nodes_validity_predicates, output)

    }

    predicate NextNodeStep<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        output: Optional<OutCommand>
    )
    {
        ( && isConditionForSafetyTrue(s)
          && output.isPresent() )
        ==> 
        (
            && var n := output.safe_get().node;
            && n in s.honest_nodes_status.Keys 
            && n in honest_nodes_validity_predicates.Keys
            && s.honest_nodes_status[n] in {DECIDED}
            && s.decided_value.isPresent()
            && output.safe_get().value == s.decided_value.safe_get()
        )
    }

    predicate is_a_valid_decided_value<D(!new, 0)>(
        s: ConsensusInstance
    )
    {
        && s.decided_value.isPresent()
        && (
            exists h_nodes |
                && h_nodes <= s.honest_nodes_validity_functions.Keys  
                && |h_nodes| >= f(|s.all_nodes|) + 1
                ::
                forall n | n in h_nodes :: 
                    exists vp: D -> bool | vp in s.honest_nodes_validity_functions[n] :: vp(s.decided_value.safe_get())       
        ) 
    }

    function add_set_of_validity_predicates<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>
    ): (new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>)
    {
        map k | k in existing_honest_nodes_validity_predicates.Keys + honest_nodes_validity_predicates.Keys
            ::
            if k in honest_nodes_validity_predicates.Keys then
                getOrDefault(existing_honest_nodes_validity_predicates, k, {}) + {honest_nodes_validity_predicates[k]}
            else 
                existing_honest_nodes_validity_predicates[k]
    }

    predicate NextConsensusDecides<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,    
        s': ConsensusInstance
    )
    {
        && honest_nodes_validity_predicates.Keys <= s.honest_nodes_status.Keys
        && s'.honest_nodes_validity_functions == add_set_of_validity_predicates(s.honest_nodes_validity_functions, honest_nodes_validity_predicates)
        && (
            || (
                && (isConditionForSafetyTrue(s) ==>
                                                    && s'.decided_value.isPresent()
                                                    && (s.decided_value.isPresent() ==> s'.decided_value == s.decided_value)
                                                    && is_a_valid_decided_value(s')
                )
                && s'.honest_nodes_status.Keys == s.honest_nodes_status.Keys
                && forall n | n in s.honest_nodes_status.Keys ::
                    if n in honest_nodes_validity_predicates then 
                        s.honest_nodes_status[n] == DECIDED ==> s'.honest_nodes_status[n] == DECIDED
                    else 
                        s'.honest_nodes_status[n] == s.honest_nodes_status[n]
                && s'.all_nodes == s.all_nodes
            ) 
            || (
                s' == s
            )
        )
     
    }    
}