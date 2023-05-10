function {:opaque} VersionIndexHelper(version: int, versions: seq<int>, lo: int, hi: int): (index: int)
  decreases hi - lo
  requires |versions| == 0 ==> lo > hi && hi == -1
  requires 0 <= lo <= |versions| 
  requires -1 <= hi < |versions|
  requires lo <= hi + 1
  requires Sorted(versions)
  requires forall k :: hi < k < |versions| ==> versions[k] > version
  requires forall k :: 0 <= k < lo ==> versions[k] <= version
  ensures -1 <= index < |versions|
  ensures index == -1 <==> (|versions| == 0 || forall k :: 0 <= k < |versions| ==> versions[k] > version)
  ensures index >= 0 <==> |versions| > 0 && versions[0] <= version
  ensures index == -1 || versions[index] <= version
  ensures forall i | 0 <= i < index :: versions[i] < version
  ensures index >= 0 ==> forall i | index < i < |versions| :: versions[i] > version
{
  if (lo > hi) then
    assert lo <= 0 || versions[lo - 1] <= version;
    lo - 1
  else
    assert |versions| > 0;
    var mid := lo + (hi - lo) / 2;
    var v := versions[mid];
    if v == version then
      mid
    else if v < version then
      VersionIndexHelper(version, versions, mid + 1, hi)
    else 
      VersionIndexHelper(version, versions, lo, mid - 1)
} 

function {:opaque} VersionIndex(version: int, versions: seq<int>): (index: int)
  requires Sorted(versions)
  ensures -1 <= index < |versions|
  ensures index >= 0 <==> |versions| > 0 && versions[0] <= version
  ensures index == -1 || IsMaxMinVersion(version, versions[index], versions)
  ensures version in versions <==> index >= 0 && |versions| > index && versions[index] == version
  ensures |versions| > 0 && version > versions[|versions| - 1] ==> index == |versions| - 1
{
  VersionIndexHelper(version, versions, 0, |versions| - 1)
}

// lemma Test(versions1: seq<int>, versions2: seq<int>) 
//   requires |versions2| >= |versions1| 
//   requires Sorted(versions1) && Sorted(versions2)
//   requires forall i | 0 <= i < |versions1| :: versions1[i] == versions2[i]
//   // ensures forall v :: VersionIndex(v, versions1) == -1 <==> VersionIndex(v, versions2) == -1
//   ensures |versions2| > |versions1| ==> 
//           forall v | v < versions2[|versions1|] :: 
//             VersionIndex(v, versions1) == VersionIndex(v, versions2)
//   ensures |versions2| == |versions1| ==>
//           forall v :: VersionIndex(v, versions1) == VersionIndex(v, versions2)
// {
//   // assert forall v | v <= versions1[|versions1| - 1] :: true;
// }


  predicate Sorted(s: seq<int>) 
{
  (forall i, j | 0 <= i < j < |s| :: 0 <= s[i] < s[j])
  && (forall i | 0 <= i < |s| :: 0 <= s[i])
}

  predicate IsMaxMinVersion(queryVersion: int, maxMinVersion: int, versions: seq<int>)
{
  maxMinVersion <= queryVersion
  && (maxMinVersion == -1 
      || (maxMinVersion in versions
          && forall v <- versions :: v < maxMinVersion || v == maxMinVersion || v > queryVersion))
}

class Node {
  ghost var Repr: set<Node>
  ghost var ValueSetsVersions: seq<int>
  ghost var ValueSets: seq<set<int>> 
  
  var leftsVersions: seq<int>
  var lefts: seq<Node?>
  var rightsVersions: seq<int>
  var rights: seq<Node?>
  var valuesVersions: seq<int>
  var values: seq<int>

  ghost  predicate isBST(version: int)  
    reads {this} + (set x | x in rights) + (set x | x in lefts)
    requires |valuesVersions| > 0 && version >= valuesVersions[0]
    requires BasicProp()
    requires Sorted(leftsVersions) && Sorted(rightsVersions) && Sorted(ValueSetsVersions) && Sorted(valuesVersions)
    requires forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions)
    requires forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions)
  {
    var v := ValueAt(version);
    var r := RightAt(version);
    var l := LeftAt(version);
    // COMMENT: times out if written in a recursive fashion, i.e., r != null ==> r.isBST() && ...)
    (r != null ==> forall v' <- r.ValueSetAt(version) :: v' > v)
    && (l != null ==> forall v' <- l.ValueSetAt(version) :: v' < v)
  }

  ghost predicate BinarySearchProp()
    reads {this} + (set x | x in lefts) + (set x | x in rights)
    requires |valuesVersions| > 0
    requires BasicProp()
    requires Sorted(leftsVersions) && Sorted(rightsVersions) && Sorted(ValueSetsVersions) && Sorted(valuesVersions)
    requires forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions)
    requires forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions)
  {
    forall v | v >= valuesVersions[0] :: isBST(v)
  }

  // ghost predicate SortedProp()
  //   reads this
  // {
  //   Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
  // }

  ghost predicate ReprProp()
    reads this, Repr
  {
    && this in Repr
    && (forall l <- lefts | l != null ::
        l in Repr && this !in l.Repr && l.Repr < Repr && l.ReprProp() 
        && l.BasicProp() && l.VersionsProp() && l.ValueSetProp() && l.BinarySearchProp()) 
    && (forall r <- rights | r != null ::
        r in Repr && this !in r.Repr && r.Repr < Repr && r.ReprProp() 
        && r.BasicProp() && r.VersionsProp() && r.ValueSetProp() && r.BinarySearchProp()) 
    // the two strong assumption does not hold for fat node method in general
    // && (forall l1 <- lefts, l2 <- lefts | l1 != null && l2 != null && l1 != l2 ::
    //     l1.Repr !! l2.Repr)
    // && (forall r1 <- rights, r2 <- rights | r1 != null && r2 != null && r1 != r2 ::
    //     r1.Repr !! r2.Repr)
    && (forall r <- rights, l <- lefts | r != null && l != null :: 
        l != r && l.Repr !! r.Repr) 
  }

  ghost predicate BasicProp()
    reads this
  {
    |ValueSetsVersions| == |ValueSets|
    && |valuesVersions| == |values|
    && |leftsVersions| == |lefts|
    && |rightsVersions| == |rights|
    && |ValueSetsVersions| > 0
    && |valuesVersions| > 0
    && |ValueSetsVersions| <= |leftsVersions| + |rightsVersions| + |valuesVersions|
    && ValueSetsVersions[0] == valuesVersions[0]
    && ValueSetsVersions[0] >= 0 
    && (|leftsVersions| > 0 ==> leftsVersions[0] > 0)
    && (|rightsVersions| > 0 ==> rightsVersions[0] > 0)
    
  }

  // ghost predicate ValueSetUnions(v: int)
  //   reads {this} + (set x | x in rights) + (set x | x in lefts)
  //   requires |valuesVersions| > 0 && v >= valuesVersions[0]
  //   requires BasicProp()
  //   requires Sorted(leftsVersions) && Sorted(rightsVersions) && Sorted(ValueSetsVersions) && Sorted(valuesVersions)
  //   requires forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions)
  //   requires forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions)
  // {
  //    ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v)
  // }

  ghost predicate ValueSetProp()
    reads {this} + (set x | x in lefts) + (set x | x in rights)
    requires VersionsProp() && BasicProp() 
    requires forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions)
    requires forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions)
  {
    // COMMENT: using forall v | ValueSetsVersions[0] <= v <= ValueSetsVersions[|ValueSetsVersions| - 1] did not work
    forall v | valuesVersions[0] <= v :: ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v)
  }

  ghost predicate VersionsProp()
    reads {this} + (set x | x in lefts) + (set x | x in rights)
  {
    && Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
    && (forall v <- ValueSetsVersions ::
        v in valuesVersions 
        || (exists l <- lefts :: l != null && v in l.ValueSetsVersions)
        || (exists r <- rights :: r != null && v in r.ValueSetsVersions))
    && (forall v <- valuesVersions :: v in ValueSetsVersions)
    && (forall v <- valuesVersions :: v in ValueSetsVersions)
    && (forall v <- leftsVersions :: v in ValueSetsVersions)
    && (forall l <- lefts | l != null :: 
          forall v <- l.ValueSetsVersions :: v in ValueSetsVersions)
    && (forall v <- rightsVersions :: v in ValueSetsVersions)
    && (forall r <- rights | r != null :: 
          forall v <- r.ValueSetsVersions :: v in ValueSetsVersions)
  }

  ghost function LeftValueSetAt(version: int) : (res: set<int>)
    reads {this} + (set x | x in lefts)
    requires BasicProp() && Sorted(leftsVersions)
    requires forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions)
    ensures LeftAt(version) == null ==> res == {}
    ensures LeftAt(version) != null ==> res == LeftAt(version).ValueSetAt(version)
  {
    var l := LeftAt(version);
    if l == null then
      {}
    else
      l.ValueSetAt(version)
  }

  ghost function RightValueSetAt(version: int) : (res: set<int>)
    reads {this} + (set x | x in rights)
    requires BasicProp() && Sorted(rightsVersions)
    requires forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions)
    ensures RightAt(version) == null ==> res == {}
    ensures RightAt(version) != null ==> res == RightAt(version).ValueSetAt(version)
  {
    var r := RightAt(version);
    if r == null then
      {}
    else
      r.ValueSetAt(version)
  }

  constructor Init(time: int, value: int)
    requires time >= 0
    ensures fresh(Repr)
    ensures lefts == []
    ensures rights == []
    ensures Repr == {this}
    ensures values == [value]
    ensures valuesVersions == [time]
    ensures ValueSets == [{value}]
    ensures ValueSetsVersions == [time]
    ensures ValueSetAt(time) == {value}
    // ensures forall v | v >= time :: ValueAt(v) == value
    ensures ReprProp() && VersionsProp() && BasicProp() && ValueSetProp() && BinarySearchProp() 
  {
    lefts := [];
    leftsVersions := [];
    rights := [];
    rightsVersions := [];
    values := [value];
    valuesVersions := [time];
    Repr := {this};
    ValueSetsVersions := [time];
    ValueSets := [{value}];
  }

  function Left(): (l: Node?)
    reads this
    ensures |lefts| == 0 ==> l == null
    ensures |lefts| > 0 ==> l == lefts[|lefts| - 1]
  {
    if |lefts| > 0 then
      lefts[|lefts| - 1]
    else
      null
  }

  function Right(): (r: Node?)
    reads this
    ensures |rights| == 0 ==> r == null
    ensures |rights| > 0 ==> r == rights[|rights| - 1]
  {
    if |rights| > 0 then
      rights[|rights| - 1]
    else
      null
  }

  function Value(): (v: int)
    reads this
    requires |values| > 0
    ensures v == values[|values| - 1]
  {
    values[|values| - 1]
  }

  ghost function ValueSet(): (s: set<int>)
    reads this
    requires |ValueSets| > 0
    ensures s == ValueSets[|ValueSets| - 1]
  {
    ValueSets[|ValueSets| - 1]
  }

  ghost function {:opaque} VersionIndexForValueSets(version: int) : (index: int)
    reads this
    requires Sorted(ValueSetsVersions)
    ensures -1 <= index < |ValueSetsVersions|
    ensures index >= 0 <==> |ValueSetsVersions| > 0 && ValueSetsVersions[0] <= version
    ensures index == -1 || IsMaxMinVersion(version, ValueSetsVersions[index], ValueSetsVersions)
    ensures version in ValueSetsVersions <==> index >= 0 && |ValueSetsVersions| > index && ValueSetsVersions[index] == version
    ensures index == VersionIndex(version, ValueSetsVersions)
  {
    VersionIndex(version, ValueSetsVersions)
  }

  ghost function {:opaque} ValueSetAt(version: int) : (res: set<int>)
    reads this
    requires Sorted(ValueSetsVersions)
    requires |ValueSetsVersions| == |ValueSets|
    ensures VersionIndexForValueSets(version) == -1 ==> res == {}
    ensures VersionIndexForValueSets(version) >= 0 ==> res in ValueSets
    ensures VersionIndexForValueSets(version) == -1 
            || res == ValueSets[VersionIndexForValueSets(version)]

  {
    var i := VersionIndexForValueSets(version);
    if i == -1 then
      {}
    else
      ValueSets[i]
  }

  function {:opaque} VersionIndexForValues(version: int) : (index: int)
    reads this
    requires Sorted(valuesVersions)
    ensures -1 <= index < |valuesVersions|
    // ensures index == -1 <=> |valuesVersions| == 0 && valuesVersions[0] > version
    ensures index >= 0 <==> |valuesVersions| > 0 && valuesVersions[0] <= version
    ensures index == -1 || IsMaxMinVersion(version, valuesVersions[index], valuesVersions)
    ensures index == VersionIndex(version, valuesVersions)
    // ensures index == -1 || valuesVersions[index] in ValueSetsVersions
    // ensures index <= VersionIndexForValueSets(version)
  {
    VersionIndex(version, valuesVersions)
  }

  function {:opaque} ValueAt(version: int): (res: int)
    reads this
    requires Sorted(valuesVersions) && |valuesVersions| == |values|
    ensures VersionIndexForValues(version) >= 0 ==> res in values
    ensures VersionIndexForValues(version) == -1
            || res == values[VersionIndexForValues(version)]
    // ensures VersionIndexForValues(version) == -1 ||
    //         res in ValueSetAt(version)
  {
    var i := VersionIndexForValues(version);
    if i == -1 then
      -1
    else
      values[i]
  }

  function {:opaque} VersionIndexForRights(version: int) : (index: int)
    reads this
    requires Sorted(rightsVersions)
    ensures -1 <= index < |rightsVersions|
    ensures index >= 0 <==> |rightsVersions| > 0 && rightsVersions[0] <= version
    ensures index == -1 || IsMaxMinVersion(version, rightsVersions[index], rightsVersions)
    ensures index == VersionIndex(version, rightsVersions)
    // ensures index == -1 || rightsVersions[index] in ValueSetsVersions
    // ensures index <= VersionIndexForValueSets(version)
  {
    VersionIndex(version, rightsVersions)
  }

  function {:opaque} RightAt(version: int) : (res: Node?)
    reads this
    requires Sorted(rightsVersions) && |rightsVersions| == |rights|
    ensures res == null || res in rights
    ensures VersionIndexForRights(version) >= 0 ==> res in rights
    ensures VersionIndexForRights(version) == -1 ==> res == null
    ensures VersionIndexForRights(version) == -1 
            || res == rights[VersionIndexForRights(version)]
  {
    var i := VersionIndexForRights(version);
    if i == -1 then
      null
    else
      rights[i]
  }

  function {:opaque} VersionIndexForLefts(version: int) : (index: int)
    reads this
    requires Sorted(leftsVersions)
    ensures -1 <= index < |leftsVersions|
    ensures index >= 0 <==> |leftsVersions| > 0 && leftsVersions[0] <= version
    ensures index == -1 || IsMaxMinVersion(version, leftsVersions[index], leftsVersions)
    ensures index == VersionIndex(version, leftsVersions)
    // ensures index == -1 || leftsVersions[index] in ValueSetsVersions
    // ensures index <= VersionIndexForValueSets(version)
  {
    VersionIndex(version, leftsVersions)
  }

  function {:opaque} LeftAt(version: int) : (res: Node?)
    reads this
    requires Sorted(leftsVersions) && |leftsVersions| == |lefts|
    ensures res == null || res in lefts
    ensures VersionIndexForLefts(version) >= 0 ==> res in lefts
    ensures VersionIndexForLefts(version) == -1 ==> res == null
    ensures VersionIndexForLefts(version) == -1 
            || res == lefts[VersionIndexForLefts(version)]
  {
    var i := VersionIndexForLefts(version);
    if i == -1 then
      null
    else
      lefts[i]
  }

  function {:opaque} Find(version: int, value: int) : (res: bool) 
    reads Repr
    requires version >= 0
    requires ReprProp() && VersionsProp() && BasicProp() && ValueSetProp() && BinarySearchProp()
    ensures res <==> value in ValueSetAt(version)
  {
    var i := VersionIndexForValues(version);
    if i == -1 then
      assert VersionIndexForValueSets(version) == -1;
      assert value !in ValueSetAt(version);
      false
    else
      assert version >= valuesVersions[0];
      assert isBST(version);  // COMMENT: crutial
      assert ValueSetAt(version) == {ValueAt(version)} + LeftValueSetAt(version) + RightValueSetAt(version); // COMMENT: crutial
      var x := ValueAt(version);
      if x > value then
        var left := LeftAt(version);
        ghost var r := RightAt(version);
        assert r != null ==> value !in r.ValueSetAt(version);
        if left == null then 
          false
        else
          left.Find(version, value)
      else if x < value then
        var right := RightAt(version);
        ghost var l := LeftAt(version);
        assert l != null ==> value !in l.ValueSetAt(version);
        if right == null then
          false
        else
          right.Find(version, value)
      else
        true
  }

  // method AddNode(node: Node?, addToRight: bool)
  //   modifies this
  //   requires node != null ==> node !in Repr
  //   requires node != null ==> 
  //     node.lefts == []
  //     && node.rights == []
  //     && node.Repr == {node}
  //     && |node.values| == 1 
  //     && |node.ValueSets| == 1
  //     && node.ReprProp() 
  //     && node.VersionsProp() 
  //     && node.BasicProp() 
  //     && node.ValueSetProp() 
  //     && node.BinarySearchProp()
  //   requires node != null && addToRight ==> AllSmallerThan(values, node.ValueSets)
  //   requires node != null && !addToRight ==> AllBiggerThan(values, node.ValueSets)
  //   requires ReprProp() && VersionsProp() && BasicProp() && ValueSetProp() && BinarySearchProp() 
  //   requires node != null ==> node.valuesVersions[0] > ValueSetsVersions[|ValueSetsVersions| - 1]
  //   ensures node != null ==> Repr == old(Repr) + {node}
  //   ensures node != null && addToRight ==> rights == old(rights) + [node] && lefts == old(lefts)
  //   ensures node != null && !addToRight ==> lefts == old(lefts) + [node] && rights == old(rights)
  //   ensures node == null <==> Repr == old(Repr)
  //   ensures ReprProp() && VersionsProp() && BasicProp() && ValueSetProp() && BinarySearchProp() 
  //   ensures node != null ==> node.values[0] in ValueSetAt(node.valuesVersions[0]) 
  // {
  //   if (node != null) {
  //     var version := node.valuesVersions[0];
  //     ghost var value := node.values[0];
  //     if (addToRight) {
  //       assert |rightsVersions| > 0 ==> rightsVersions[|rightsVersions| - 1] in ValueSetsVersions;
  //       assert |rightsVersions| > 0 ==> version > rightsVersions[|rightsVersions| - 1];
  //       rights := rights + [node];
  //       rightsVersions := rightsVersions + [version];
  //       assert leftsVersions == old(leftsVersions);
  //       assert rightsVersions == old(rightsVersions) + [version];
  //     } else {
  //       assert |leftsVersions| > 0 ==> leftsVersions[|leftsVersions| - 1] in ValueSetsVersions;
  //       assert |leftsVersions| > 0 ==> version > leftsVersions[|leftsVersions| - 1];
  //       lefts := lefts + [node];
  //       leftsVersions := leftsVersions + [version];
  //       assert rightsVersions == old(rightsVersions);
  //       assert leftsVersions == old(leftsVersions) + [version];
  //     }

  //     assert(Sorted(leftsVersions));
  //     assert(Sorted(rightsVersions));

  //     Repr := Repr + {node};
  //     ValueSets := ValueSets + [ValueSet() + {value}];
  //     ValueSetsVersions := ValueSetsVersions + [version];

  //     assert ValueSetsVersions == old(ValueSetsVersions) + [version];
  //     assert Sorted(ValueSetsVersions);

  //     assert forall v | ValueSetsVersions[0] <= v :: ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v) by {
  //         assert forall v | ValueSetsVersions[0] <= v < version :: ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v) by {
  //         assert forall v | ValueSetsVersions[0] <= v < version :: ValueSetAt(v) == old(ValueSetAt(v)) by {
  //           assert forall v | ValueSetsVersions[0] <= v < version ::
  //                 old(VersionIndexForValueSets(v)) == VersionIndex(v, old(ValueSetsVersions))
  //                 && VersionIndexForValueSets(v) == VersionIndex(v, ValueSetsVersions);
  //           Test(old(ValueSetsVersions), ValueSetsVersions);
  //           assert forall v | ValueSetsVersions[0] <= v < version :: VersionIndexForValueSets(v) == old(VersionIndexForValueSets(v));
  //         }

  //         assert forall v | ValueSetsVersions[0] <= v < version :: LeftValueSetAt(v) == old(LeftValueSetAt(v)) by {
  //           assert forall v | ValueSetsVersions[0] <= v < version ::
  //                 old(VersionIndexForLefts(v)) == VersionIndex(v, old(leftsVersions))
  //                 && VersionIndexForLefts(v) == VersionIndex(v, leftsVersions);
  //           Test(old(leftsVersions), leftsVersions);
  //           assert forall v | ValueSetsVersions[0] <= v < version :: VersionIndexForLefts(v) == old(VersionIndexForLefts(v));
  //           assert forall v | ValueSetsVersions[0] <= v < version :: LeftAt(v) == old(LeftAt(v));
  //         }

  //         assert  forall v | ValueSetsVersions[0] <= v < version :: RightValueSetAt(v) == old(RightValueSetAt(v)) by {
  //           assert forall v | ValueSetsVersions[0] <= v < version ::
  //                 old(VersionIndexForRights(v)) == VersionIndex(v, old(rightsVersions))
  //                 && VersionIndexForRights(v) == VersionIndex(v, rightsVersions);
  //           Test(old(rightsVersions), rightsVersions);
  //           assert forall v | ValueSetsVersions[0] <= v < version :: VersionIndexForRights(v) == old(VersionIndexForRights(v));
  //           assert forall v | ValueSetsVersions[0] <= v < version :: RightAt(v) == old(RightAt(v));
  //         }
  //       }

  //       assert forall v | version < v :: ValueSetAt(v) == ValueSetAt(version);
  //       assert forall v | version < v :: LeftValueSetAt(v) == LeftValueSetAt(version);
  //       assert forall v | version < v :: RightValueSetAt(v) == RightValueSetAt(version);

  //       assume false;
        
  //       assert ValueSetAt(version) == {ValueAt(version)} + LeftValueSetAt(version) + RightValueSetAt(version) by {
  //         assert ValueAt(version) == old(ValueAt(version));
  //         assert !addToRight ==> (LeftAt(version) == node
  //                               && LeftValueSetAt(version) == {value} + old(LeftValueSetAt(version)) && RightValueSetAt(version) == old(RightValueSetAt(version)));
  //         assert addToRight ==> (RightAt(version) == node
  //                               && RightValueSetAt(version) == {value} + old(RightValueSetAt(version)) && LeftValueSetAt(version) == old(LeftValueSetAt(version)));
  //         assert VersionIndexForValueSets(version) == |ValueSetsVersions| - 1;
  //         assert ValueSetAt(version) == ValueSets[|ValueSetsVersions| - 1];

  //         // assert oldVS == ValueSets[|ValueSets| - 2];
  //         // assert oldVS == old(ValueSetAt(version));
  //         assert ValueSetAt(version) == old(ValueSetAt(version)) + {value};
  //       }

        

  //     }


  //   }
  // }

  lemma VersionsLemma(version: int)
    requires BasicProp() && VersionsProp()
    requires version > ValueSetsVersions[|ValueSetsVersions| - 1]
    ensures |rightsVersions| > 0 ==> version > rightsVersions[|rightsVersions| - 1]
    ensures |leftsVersions| > 0 ==> version > leftsVersions[|leftsVersions| - 1]
    ensures version > valuesVersions[|valuesVersions| - 1]
  {
    assert |rightsVersions| > 0 ==> rightsVersions[|rightsVersions| - 1] in ValueSetsVersions;
    assert |leftsVersions| > 0 ==> leftsVersions[|leftsVersions| - 1] in ValueSetsVersions;
    assert valuesVersions[|valuesVersions| - 1] in ValueSetsVersions;
  }

  method Insert(version: int, value: int) returns (res: Node?) 
    modifies Repr
    decreases Repr
    requires ReprProp() && BasicProp() && VersionsProp() && ValueSetProp() && BinarySearchProp()
    requires version > ValueSetsVersions[|ValueSetsVersions| - 1]
    ensures res != null ==> fresh(res) && Repr == old(Repr) + {res}
    ensures res == null ==> Repr == old(Repr)
    ensures BasicProp() && VersionsProp() 
    // COMMENT: the below two lines have to be written as postconditions instead of assertions inside body
    ensures forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions)
    ensures forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions)
    ensures ValueSetProp()
    // ensures res != null ==> res.ReprProp() && res.BasicProp() && res.VersionsProp() && res.ValueSetProp() && res.BinarySearchProp()
    // ensures res != null ==> 
    //   ValueSetsVersions == old(ValueSetsVersions) + [version]
    //   && ValueSets == old(ValueSets) + [old(ValueSetAt(version)) + { value }]
    // ensures value < Value() && res != null ==>
    //   leftsVersions == old(leftsVersions) + [version]
    //   && lefts == old(lefts) + [res]
    //   && rightsVersions == old(rightsVersions)
    //   && rights == old(rights)
    // ensures value > Value() && res != null ==> 
    //   rightsVersions == old(rightsVersions) + [version]
    //   && rights == old(rights) + [res]
    //   && leftsVersions == old(leftsVersions)
    //   && lefts == old(lefts)
    // ensures ValueSetUnions(version) 
    // ensures forall v | ValueSetsVersions[0] <= v < version :: ValueSetAt(v) == old(ValueSetAt(v))
    // ensures forall v | ValueSetsVersions[0] <= v < version :: LeftValueSetAt(v) == old(LeftValueSetAt(v))
    // ensures forall v | ValueSetsVersions[0] <= v < version :: RightValueSetAt(v) == old(RightValueSetAt(v))
    // ensures forall v | ValueSetsVersions[0] <= v < version :: ValueSetUnions(v)
    // ensures res == null <==> Repr == old(Repr) && ValueSets == old(ValueSets) && value in old(ValueSetAt(version))
    
    // ensures BinarySearchProp() && ValueSetProp()
    // ensures value in ValueSetAt(version) 
  {
    var x := Value();
    VersionsLemma(version);

    if x > value {
      assume false;
      var left := Left();
      if left == null { 
        res := new Node.Init(version, value);
      } else {
        res := left.Insert(version, value);
      }
    } else if x < value {
      var right := Right();
      if right == null {
        res := new Node.Init(version, value);        
        rights := rights + [res];
        rightsVersions := rightsVersions + [version];
        Repr := Repr + {res};
        ValueSets := ValueSets + [ValueSet() + {value}];
        ValueSetsVersions := ValueSetsVersions + [version];
        
        assert res.BasicProp() && Sorted(res.ValueSetsVersions);
        assert Sorted(rightsVersions);
        assert Sorted(ValueSetsVersions);
        
        assert leftsVersions == old(leftsVersions);
        assert lefts == old(lefts);

        assume forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions);
        assume forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions);
        // assert ValueSetAt(version) == {ValueAt(version)} + LeftValueSetAt(version) + RightValueSetAt(version) by {
        //   assert ValueSetAt(version) == old(ValueSetAt(version)) + {value};
        //   assert ValueAt(version) == old(ValueAt(version));
        //   assert LeftValueSetAt(version) == old(LeftValueSetAt(version));
        //   assert RightValueSetAt(version) == old(RightValueSetAt(version)) + {value};
        // }

      } else {
        assume false;
        res := right.Insert(version, value);
        if (res != null) {
          assert Sorted(rightsVersions);
          Repr := Repr + {res};
          ValueSets := ValueSets + [ValueSet() + {value}];
          ValueSetsVersions := ValueSetsVersions + [version];
          assert Sorted(ValueSetsVersions);
          assert valuesVersions == old(valuesVersions);
          assert values == old(values);
        }
      }
    } else {
      assume false;
      res := null;

      assert rights == old(rights);
      assert lefts == old(lefts);
      assume forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions);
      assume forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions);
      // assert ValueSetsVersions == old(ValueSetsVersions);
      // assert rightsVersions == old(rightsVersions);
      // assert leftsVersions == old(leftsVersions);
      // assert ValueSets == old(ValueSets);
      
    }

    assert forall l <- lefts | l != null :: l.BasicProp() && Sorted(l.ValueSetsVersions);
    assert forall r <- rights | r != null :: r.BasicProp() && Sorted(r.ValueSetsVersions);

    // assert valuesVersions == old(valuesVersions);
    // assert values == old(values);
  }
}