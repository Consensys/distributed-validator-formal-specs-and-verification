include "../utils/types.dfy"
include "../utils/common-functions.dfy"

import opened Types
import opened CommonFunctions

lemma {:axiom} compute_domain_properties(dom1 : DomainTypes, ep1: Epoch, dom2: DomainTypes, ep2: Epoch)
requires compute_domain(dom1, ep1) == compute_domain(dom2, ep2) 
ensures dom1 == dom2 && ep1 == ep2           

lemma {:axiom} hash_tree_root_properties<T>(d1: T, d2: T)
requires hash_tree_root(d1) == hash_tree_root(d2)
ensures d1 == d2