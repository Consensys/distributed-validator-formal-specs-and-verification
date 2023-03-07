include "../../common/block_proposer/block_types.dfy"
include "../../common/block_proposer/block_common_functions.dfy"

import opened Block_Types
import opened Block_Common_Functions

lemma {:axiom} compute_domain_properties(dom1 : DomainTypes, ep1: Epoch, dom2: DomainTypes, ep2: Epoch)
requires compute_domain(dom1, ep1) == compute_domain(dom2, ep2) 
ensures dom1 == dom2 && ep1 == ep2           

lemma {:axiom} hash_tree_root_properties<T>(d1: T, d2: T)
requires hash_tree_root(d1) == hash_tree_root(d2)
ensures d1 == d2

lemma minOfSetOfIntExists(s: set<int>)
requires s != {}
ensures exists min :: && min in s 
                      && forall e | e in s :: min <= e 
{
    if |s| == 1 {
        var e :| e in s;
        assert |s - {e}| == 0;
    } 
    else
    {
        var e :| e in s;
        var sMinusE := s - {e};
        assert |s| > 1;
        assert s == sMinusE + {e};
        assert |sMinusE| > 0;
        minOfSetOfIntExists(sMinusE);
        var mMinusE :| mMinusE in sMinusE && forall e' | e' in sMinusE :: e' >= mMinusE;
    }    
}  
