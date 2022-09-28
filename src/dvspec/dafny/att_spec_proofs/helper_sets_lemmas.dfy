// From QBFT's repository

include "../commons.dfy"


module Helper_Sets_Lemmas {
    import opened CommonFunctions

lemma ThingsIKnowAboutSubset<T>(x:set<T>, y:set<T>)
    requires x<y;
    ensures |x|<|y|;
{
    if (x!={}) {
        var e :| e in x;
        ThingsIKnowAboutSubset(x-{e}, y-{e});
    }
}

lemma SubsetCardinality<T>(x:set<T>, y:set<T>)
    ensures x<y ==> |x|<|y|;
    ensures x<=y ==> |x|<=|y|;
{
    if (x<y) {
        ThingsIKnowAboutSubset(x, y);
    }
    if (x==y) { // OBSERVE the other case
    }
}

lemma ItIsASingletonSet<T>(foo:set<T>, x:T)
    requires foo=={x};
    ensures |foo|==1;
{
}

lemma ThingsIKnowAboutASingletonSet<T>(foo:set<T>, x:T, y:T)
    requires |foo|==1;
    requires x in foo;
    requires y in foo;
    ensures x==y;
{
    if (x!=y) {
        assert {x} < foo;
        ThingsIKnowAboutSubset({x}, foo);
        assert |{x}| < |foo|;
        assert |foo|>1;
        assert false;
    }
}

predicate Injective<X(!new), Y(!new)>(f:X-->Y)
  reads f.reads;
  requires forall x :: f.requires(x);
{
  forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
}

// predicate InjectiveOverSimp<X, Y>(xs:set<X>, f:X-->Y)
//   reads f.reads;
//   requires forall x :: x in xs ==> f.requires(x);
// {
//   forall x1, x2 :: x1 in xs && x2 in xs && f(x1) == f(x2) ==> x1 == x2
// }

predicate InjectiveOver<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
  reads f.reads;
  requires forall x :: x in xs ==> f.requires(x);
{
  forall x1, x2 :: x1 in xs && x2 in xs && f(x1) in ys && f(x2) in ys && f(x1) == f(x2) ==> x1 == x2
}

predicate InjectiveOverSeq<X, Y>(xs:seq<X>, ys:set<Y>, f:X->Y)
  reads f.reads;
  requires forall x :: x in xs ==> f.requires(x);
{
  forall x1, x2 :: x1 in xs && x2 in xs && f(x1) in ys && f(x2) in ys && f(x1) == f(x2) ==> x1 == x2
}

lemma lemma_MapSetCardinality<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
  requires forall x :: f.requires(x);
  requires Injective(f);
  requires forall x :: x in xs <==> f(x) in ys;
  requires forall y :: y in ys ==> exists x :: x in xs && y == f(x);
  ensures  |xs| == |ys|;
{
  if (xs != {})
  {
    var x :| x in xs;
    var xs' := xs - {x};
    var ys' := ys - {f(x)};
    lemma_MapSetCardinality(xs', ys', f);
  }
}

// lemma lemma_MapSetCardinalityOverSImp<X, Y>(xs:set<X>, f:X-->Y)
//   requires forall x :: x in xs ==> f.requires(x);
//   requires InjectiveOverSimp(xs, f);
//   requires forall y :: y in ys ==> exists x :: x in xs && y == f(x);
//   ensures  |xs| == |ys|;
// {
//   if (xs != {})
//   {
//     var x :| x in xs;
//     var xs' := xs - {x};
//     var ys' := ys - {f(x)};
//     lemma_MapSetCardinalityOver(xs', ys', f);
//   }
// }

lemma lemma_MapSetCardinalityOver<X, Y>(xs:set<X>, ys:set<Y>, f:X-->Y)
  requires forall x :: x in xs ==> f.requires(x);
  requires InjectiveOver(xs, ys, f);
  requires forall x :: x in xs ==> f(x) in ys;
  requires forall y :: y in ys ==> exists x :: x in xs && y == f(x);
  ensures  |xs| == |ys|;
{
  if (xs != {})
  {
    var x :| x in xs;
    var xs' := xs - {x};
    var ys' := ys - {f(x)};
    lemma_MapSetCardinalityOver(xs', ys', f);
  }
}

lemma lemma_MapSubsetCardinalityOver<X, Y>(xs:set<X>, ys:set<Y>, f:X->Y)
  requires forall x :: x in xs ==> f.requires(x);
  requires InjectiveOver(xs, ys, f);
  requires forall x :: x in xs ==> f(x) in ys;
  ensures  |xs| <= |ys|;
{
  if (xs != {})
  {
    var x :| x in xs;
    var xs' := xs - {x};
    var ys' := ys - {f(x)};
    lemma_MapSubsetCardinalityOver(xs', ys', f);
  }
}

lemma lemma_MapSubsetCardinalityOverNoInjective<T,T2>(s:set<T>, s2: set<T2>, f:T --> T2)
requires forall m | m in s :: f.requires(m)
requires s2 == set m | m in s :: f(m)
requires |s| > 0 
ensures |s2| > 0
{
  var e :| e in s;

  assert f(e) in s2;
}

lemma lemma_MapSubseqCardinalityOver<X, Y>(xs:seq<X>, ys:set<Y>, f:X->Y)
  requires forall x :: x in xs ==> f.requires(x);
  requires forall i, j :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j];
  requires InjectiveOverSeq(xs, ys, f);
  requires forall x :: x in xs ==> f(x) in ys;
  ensures  |xs| <= |ys|;
{
  if (xs != [])
  {
    var x := xs[0];
    var xs' := xs[1..];
    var ys' := ys - {f(x)};
    forall x' | x' in xs'
        ensures f(x') in ys';
    {
        assert x' in xs;
        assert f(x') in ys;
        if f(x') == f(x)
        {
            assert x in xs && x' in xs && f(x) in ys && f(x') in ys && f(x') == f(x);
            assert x' == x;
        }
    }
    forall x1, x2 | x1 in xs' && x2 in xs' && f(x1) in ys' && f(x2) in ys' && f(x1) == f(x2)
        ensures x1 == x2;
    {
        assert x1 in xs && x2 in xs && f(x1) in ys && f(x2) in ys';
    }
    lemma_MapSubseqCardinalityOver(xs', ys', f);
  }
}

function MapSetToSet<X(!new), Y>(xs:set<X>, f:X->Y):set<Y>
  reads f.reads;
  requires forall x :: f.requires(x);
  requires Injective(f);
  ensures  forall x :: x in xs <==> f(x) in MapSetToSet(xs, f);
  ensures  |xs| == |MapSetToSet(xs, f)|;
{
  var ys := set x | x in xs :: f(x); 
  lemma_MapSetCardinality(xs, ys, f);
  ys
}

function MapSetToSetOver<X, Y>(xs:set<X>, f:X->Y):set<Y>
  reads f.reads;
  requires forall x :: x in xs ==> f.requires(x);
  requires InjectiveOver(xs, set x | x in xs :: f(x), f);
  ensures  forall x :: x in xs ==> f(x) in MapSetToSetOver(xs, f);
  ensures  |xs| == |MapSetToSetOver(xs, f)|;
{
  var ys := set x | x in xs :: f(x); 
  lemma_MapSetCardinalityOver(xs, ys, f);
  ys
}

function MapSeqToSet<X(!new), Y>(xs:seq<X>, f:X->Y):set<Y>
  reads f.reads;
  requires forall x :: f.requires(x);
  requires Injective(f);
  ensures  forall x :: x in xs <==> f(x) in MapSeqToSet(xs, f);
{
  set x | x in xs :: f(x)
}

lemma lemma_SubsetCardinality<X>(xs:set<X>, ys:set<X>, f:X->bool)
  requires forall x :: x in xs ==> f.requires(x);
  requires forall x :: x in ys ==> x in xs && f(x);
  ensures  |ys| <= |xs|;
{
  if (ys != {})
  {
    var y :| y in ys;
    var xs' := xs - {y};
    var ys' := ys - {y};
    lemma_SubsetCardinality(xs', ys', f);
  }
}

function MakeSubset<X(!new)>(xs:set<X>, f:X->bool):set<X>
  reads f.reads;
  requires forall x :: x in xs ==> f.requires(x);
  ensures  forall x :: x in MakeSubset(xs, f) <==> x in xs && f(x);
  ensures  |MakeSubset(xs, f)| <= |xs|;
{
  var ys := set x | x in xs && f(x);
  lemma_SubsetCardinality(xs, ys, f);
  ys
}

/* examples:
function{:opaque} setAdd1(xs:set<int>):set<int>
  ensures forall x :: x in xs <==> x + 1 in setAdd1(xs);
  ensures |xs| == |setAdd1(xs)|;
{
  MapSetToSet(xs, x => x + 1)
}
function{:opaque} setPos(xs:set<int>):set<int>
  ensures forall x :: x in setPos(xs) <==> x in xs && x > 0;
{
  MakeSubset(xs, x => x > 0)
}
*/

lemma lemma_UnionCardinality<X>(xs:set<X>, ys:set<X>, us:set<X>)
    requires us==xs+ys;
    ensures |us| >= |xs|;
    decreases ys;
{
    if (ys=={}) {
    } else {
        var y :| y in ys;
        if (y in xs) {
            var xr := xs - {y};
            var yr := ys - {y};
            var ur := us - {y};
            lemma_UnionCardinality(xr, yr, ur);
        } else {
            var ur := us - {y};
            var yr := ys - {y};
            lemma_UnionCardinality(xs, yr, ur);
        }
    }
}

function SetOfNumbersInRightExclusiveRange(a:int, b:int):set<int>
    requires a <= b;
    ensures forall opn :: a <= opn < b ==> opn in SetOfNumbersInRightExclusiveRange(a, b);
    ensures forall opn :: opn in SetOfNumbersInRightExclusiveRange(a, b) ==> a <= opn < b;
    ensures |SetOfNumbersInRightExclusiveRange(a, b)| == b-a;
    decreases b-a;
{
    if a == b then {} else {a} + SetOfNumbersInRightExclusiveRange(a+1, b)
}

lemma lemma_CardinalityOfBoundedSet(s:set<int>, a:int, b:int)
    requires forall opn :: opn in s ==> a <= opn < b;
    requires a <= b;
    ensures  |s| <= b-a;
{
    var range := SetOfNumbersInRightExclusiveRange(a, b);
    forall i | i in s
        ensures i in range;
    {
    }
    assert s <= range;
    SubsetCardinality(s, range);
}


function intsetmax(s:set<int>):int
    requires |s| > 0;
    ensures  var m := intsetmax(s);
             m in s && forall i :: i in s ==> m >= i;
{
    var x :| x in s;
    if |s| == 1 then
        assert |s - {x}| == 0;
        x
    else
        var sy := s - {x};
        var y := intsetmax(sy);
        assert forall i :: i in s ==> i in sy || i == x;
        if x > y then x else y
}

    lemma lemmaQuorumIntersection<T(==)>(nodes:set<T>, byz:set<T>, Q1:set<T>, Q2:set<T>)
    requires nodes != {}
    requires Q1 <= nodes
    requires Q2 <= nodes
    // requires byz <= nodes
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
                        <= {SubsetCardinality(Q1 + Q2, nodes);}
                        |nodes|; 
                    }
                |Q1| + |Q2| - |nodes|;
            }
            |Q1| + |Q2| - |byz| - |(Q1*Q2) + hon|;
            >= {SubsetCardinality((Q1*Q2) + hon, nodes);}
            |Q1| + |Q2| - |byz| - |nodes|;
            >=
            2 * quorum(|nodes|)- |nodes| - f(|nodes|);
            >=
            1;
        }

    }

    lemma lemmaThereExistsAnHonestInQuorum<T(==)>(nodes:set<T>, byz:set<T>, Q1:set<T>)
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
            {SubsetCardinality(Q1 + hon, nodes);}
            // calc {
            //     |Q1|;
            //     |Q1| + |Q2| - |Q1 + Q2|;
            //     >= calc {
            //             |Q1 + Q2|; 
            //             <= {SubsetCardinality(Q1 + Q2, nodes);}
            //             |nodes|; 
            //         }
            //     |Q1| + |Q2| - |nodes|;
            // }
            |Q1|  - |byz|;
            >=
            quorum(|nodes|) - f(|nodes|);
            >=
            1;
        }        
    }   

    lemma lemmaThereExistsAnHonestInQuorum2<T(==)>(nodes:set<T>, byz: set<T>, hon:set<T>)
    requires nodes != {}
    requires hon <= nodes
    requires byz <= nodes
    requires |hon| >= quorum(|nodes|) - |byz|
    requires |byz| <= f(|nodes|)
    requires hon * byz == {}
    ensures hon != {}
    {
        lemmaEmptyIntersectionImpliesDisjointness(hon, byz);
        var hon_byz := hon + byz;


        assert |hon_byz| >= quorum(|nodes|);

        lemmaThereExistsAnHonestInQuorum(nodes, byz, hon_byz);

        assert hon != {};
    }       

    lemma test_quorum(n: nat)
    ensures quorum(n) * 3 >= 2 * n
    { }   

    lemma test_f(n: nat)
    requires 0 < n
    ensures f(n) * 3 + 1 <= n
    { }  

    lemma lemmaQuorumIsGreaterThan2F<T(==)>(nodes:set<T>)
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
            {SubsetCardinality(S1 + S2, subset);}
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

    lemma lemmaEmptyIntersectionImpliesDisjointness<T>(
      s1: set<T>,
      s2: set<T>
    )
    requires s1 * s2 == {}
    ensures s1 !! s2 
    {
      if s1 == {} && s2 == {}
      {
        assert s1 !! s2 ;
      }
      else if s1 == {} 
      {
        assert s1 !! s2 ;
      }  
      else if s2 == {} 
      {
        assert s1 !! s2 ;
      }           
      else if !(s1 !! s2)
      {
        var e :| e in s1 && e in s2;
        assert e in (s1 * s2);
        assert (s1 * s2) != {};
        assert false;
      }
    }

    lemma lemmaInUnion<T(==)>(S: set<T>, S1: set<T>, S2: set<T>, m: T)
    requires S == S1 + S2
    requires m in S
    ensures m in S1 || m in S2
    {}

    lemma lemmaMapKeysHasOneEntryInItems<K, V>(m: map<K, V>, k: K)  
    requires k in m.Keys
    ensures exists i :: i in m.Items && i.0 == k 
    {
        assert (k, m[k]) in m.Items;
    }       

    lemma lemmaFromMemberToSingletonSet<T>(e: T, S: set<T>)
    requires e in S
    ensures {e} <= S
    {}

    lemma lemmaUnionOfSubsets<T>(S1: set<T>, S2: set<T>, S: set<T>)
    requires S1 <= S && S2 <= S
    ensures S1 + S2 <= S
    {}

    lemma lemmaSubsetOfSubset<T>(S1: set<T>, S2: set<T>, S3: set<T>)
    requires S1 <= S2 && S2 <= S3
    ensures S1  <= S3
    {}
}