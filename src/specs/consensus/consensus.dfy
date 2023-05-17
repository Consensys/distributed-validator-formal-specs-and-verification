include "../../common/commons.dfy"

// Note: Only safety properties are expressed at the moment.
module Consensus
{
    import opened Types 
    import opened Common_Functions

    predicate condition_for_safety_is_true<D(!new, 0)>(
        s: ConsensusInstance
    )
    {
        var byz := s.all_nodes - s.honest_nodes_status.Keys;
        |byz| <= f(|s.all_nodes|)
    }

    predicate init<D(!new, 0)>(
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

    predicate next<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,        
        s': ConsensusInstance,
        output: Optional<OutCommand>
    )
    {
        && next_consensus_decides(s, honest_nodes_validity_predicates, s')
        && next_node_step(s', honest_nodes_validity_predicates, output)
    }

    predicate next_node_step<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,
        output: Optional<OutCommand>
    )
    {
        ( && condition_for_safety_is_true(s)
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

    predicate decided_value_is_based_on_validity_predicates_from_quorum<D(!new, 0)>(
        s: ConsensusInstance,
        h_nodes: set<BLSPubkey>
    )
    {
        && s.decided_value.isPresent()
        && h_nodes <= s.honest_nodes_validity_functions.Keys  
        && var byz := s.all_nodes - s.honest_nodes_status.Keys;
        && |h_nodes| >= quorum(|s.all_nodes|) - |byz|
        && (
            forall n | n in h_nodes :: 
                exists vp: D -> bool | vp in s.honest_nodes_validity_functions[n] :: vp(s.decided_value.safe_get())  
        )          
    }

    predicate decided_value_is_valid<D(!new, 0)>(
        s: ConsensusInstance
    )
    {
       exists h_nodes :: decided_value_is_based_on_validity_predicates_from_quorum(s, h_nodes)            
    }

    function f_add_set_of_validity_predicates<D(!new, 0)>(
        existing_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>
    ): (new_honest_nodes_validity_predicates: map<BLSPubkey, set<D -> bool>>)
    {
        map k | k in existing_honest_nodes_validity_predicates.Keys + honest_nodes_validity_predicates.Keys
            ::
            if k in honest_nodes_validity_predicates.Keys then
                get_or_default(existing_honest_nodes_validity_predicates, k, {}) + {honest_nodes_validity_predicates[k]}
            else 
                existing_honest_nodes_validity_predicates[k]
    }

    predicate next_consensus_decides<D(!new, 0)>(
        s: ConsensusInstance,
        honest_nodes_validity_predicates: map<BLSPubkey, D -> bool>,    
        s': ConsensusInstance
    )
    {
        && honest_nodes_validity_predicates.Keys <= s.honest_nodes_status.Keys
        && s'.honest_nodes_validity_functions == f_add_set_of_validity_predicates(s.honest_nodes_validity_functions, honest_nodes_validity_predicates)
        && (
            || (
                && (condition_for_safety_is_true(s) ==>
                                                    && s'.decided_value.isPresent()
                                                    && (s.decided_value.isPresent() ==> s'.decided_value == s.decided_value)
                                                    && decided_value_is_valid(s')
                )
                && s'.honest_nodes_status.Keys == s.honest_nodes_status.Keys
                && (forall n | n in s.honest_nodes_status.Keys ::
                    if n in honest_nodes_validity_predicates.Keys then 
                        s.honest_nodes_status[n] == DECIDED ==> s'.honest_nodes_status[n] == DECIDED
                    else 
                        s'.honest_nodes_status[n] == s.honest_nodes_status[n]
                )
                && s'.all_nodes == s.all_nodes
            ) 
            || (
                s' == s
            )
        )
    }    
}