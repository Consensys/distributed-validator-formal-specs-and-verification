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
    )    

    // Move functions f, quorum, and test_quorum to file commons.dfy




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
        // exists s'': ConsensusInstance ::
            // First we let the consensus protocol and the various nodes possibly decide on a value
            && NextConsensusDecides(s, honest_nodes_validity_predicates, s')
            // Then we let the node take an input/output step
            && NextNodeStep(s', honest_nodes_validity_predicates, output)

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

    predicate is_a_valid_decided_value_according_to_set_of_nodes<D(!new, 0)>(
        s: ConsensusInstance,
        h_nodes: set<BLSPubkey>
    )
    {
        && s.decided_value.isPresent()
        && h_nodes <= s.honest_nodes_validity_functions.Keys  
        && var byz := s.all_nodes - s.honest_nodes_status.Keys;
            |h_nodes| >= quorum(|s.all_nodes|) - |byz|
        && (
            forall n | n in h_nodes :: 
                exists vp: D -> bool | vp in s.honest_nodes_validity_functions[n] :: vp(s.decided_value.safe_get())  
        )          
    }

    // If n = 5, then f(5) = 1 and quorum(n) = 4.
    // Therefore, f(5) + 1 < quorum(5) - f(5).
    predicate is_a_valid_decided_value<D(!new, 0)>(
        s: ConsensusInstance
    )
    {
       exists h_nodes :: is_a_valid_decided_value_according_to_set_of_nodes(s, h_nodes)            
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