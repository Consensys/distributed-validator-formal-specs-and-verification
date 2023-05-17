include "../../common/commons.dfy"

module Quorum_Lemmas {
    import opened Common_Functions
    import opened Set_Seq_Helper

    lemma lemmaQuorumIntersection<T(==)>(nodes: set<T>, byz: set<T>, Q1: set<T>, Q2: set<T>)
    requires nodes != {}
    requires Q1 <= nodes
    requires Q2 <= nodes
    requires |Q1| >= quorum(|nodes|)
    requires |Q2| >= quorum(|nodes|)
    requires |byz| <= f(|nodes|)
    ensures var hon := nodes - byz; Q1 * Q2 * hon != {}
    {
        var hon := nodes - byz;

        calc {
            |Q1 * Q2 * hon|;
            ==
            |(Q1*Q2) * hon|;
            ==
            |Q1*Q2| + |hon| - |(Q1*Q2) + hon|;
            >= 
            |Q1*Q2| + |nodes| - |byz| - |(Q1*Q2) + hon|;
            >= calc {
                |Q1 * Q2|;
                |Q1| + |Q2| - |Q1 + Q2|;
                >= calc {
                        |Q1 + Q2|; 
                        <= {lem_card_of_subset_is_not_greater_than_card_of_set(Q1 + Q2, nodes);}
                        |nodes|; 
                    }
                |Q1| + |Q2| - |nodes|;
            }
            |Q1| + |Q2| - |byz| - |(Q1*Q2) + hon|;
            >= {lem_card_of_subset_is_not_greater_than_card_of_set((Q1*Q2) + hon, nodes);}
            |Q1| + |Q2| - |byz| - |nodes|;
            >=
            2 * quorum(|nodes|)- |nodes| - f(|nodes|);
            >=
            1;
        }

    }

    lemma lemmaThereExistsAnHonestInQuorum<T(==)>(nodes: set<T>, byz: set<T>, Q1: set<T>)
    requires nodes != {}
    requires Q1 <= nodes
    requires |Q1| >= quorum(|nodes|)
    requires |byz| <= f(|nodes|)
    ensures var hon := nodes - byz; Q1 * hon != {}
    {
        var hon := nodes - byz;

        calc {
            |Q1 * hon|;
            ==
            |Q1| + |hon| - |Q1 + hon|;
            >= 
            |Q1| + |nodes| - |byz| - |Q1 + hon|;
            >= 
            {lem_card_of_subset_is_not_greater_than_card_of_set(Q1 + hon, nodes);}
            |Q1|  - |byz|;
            >=
            quorum(|nodes|) - f(|nodes|);
            >=
            1;
        }        
    }   

    lemma lemmaThereExistsAnHonestInQuorum2<T(==)>(nodes: set<T>, byz: set<T>, hon: set<T>)
    requires nodes != {}
    requires hon <= nodes
    requires byz <= nodes
    requires |hon| >= quorum(|nodes|) - |byz|
    requires |byz| <= f(|nodes|)
    requires hon * byz == {}
    ensures hon != {}
    {
        lem_empty_intersection_implies_disjointness(hon, byz);
        var hon_byz := hon + byz;


        assert |hon_byz| >= quorum(|nodes|);

        lemmaThereExistsAnHonestInQuorum(nodes, byz, hon_byz);

        assert hon != {};
    }       

    

    lemma lemmaQuorumIsGreaterThan2F<T(==)>(nodes: set<T>)
    requires |nodes| > 0
    ensures quorum(|nodes|) > 2*f(|nodes|)
    { }

    lemma lemmaIntersectionOfHonestNodesInTwoQuorumsIsNotEmpty<T(==)>(
        nodes: set<T>, subset: set<T>, S1: set<T>, S2: set<T>)
    requires |nodes| > 0 
    requires |subset| >= quorum(|nodes|)
    requires subset <= nodes && S1 <= subset && S2 <= subset
    requires |S1| + |S2| > |subset|
    ensures S1 * S2 != {}
    { 
        calc {
            |S1 * S2|;
            ==
            |S1| + |S2| - |S1 + S2|;
            >
            |subset| - |S1 + S2|;            
            >=
            {lem_card_of_subset_is_not_greater_than_card_of_set(S1 + S2, subset);}
            |subset| - |subset|;
            ==
            0;
        }
    }

    lemma lemmaQuorumAndF<T(==)>(nodes: set<T>)
    requires |nodes| > 0 
    ensures && var n := |nodes|;
            && 2 * quorum(n) > n + f(n)
    {}
}