function VersionIndexHelper(version: int, versions: seq<int>, lo: int, hi: int): (index: int)
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
  // ensures index == -1 || IsMaxMinVersion(version, versions[index], versions)
  ensures index == -1 || IsMaxMinVersionIndex(version, index, versions)
  ensures version in versions <==> index >= 0 && |versions| > index && versions[index] == version
  ensures |versions| > 0 && version > versions[|versions| - 1] ==> index == |versions| - 1
  // ensures |versions| == 0 ==> index == -1
{
  VersionIndexHelper(version, versions, 0, |versions| - 1)
}

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

predicate IsMaxMinVersionIndex(queryVersion: int, index: int, versions: seq<int>)
  requires Sorted(versions)
  requires 0 <= index < |versions|
{
  (forall i | 0 <= i < index :: versions[i] < queryVersion)
  && versions[index] <= queryVersion
  && (forall i | index < i < |versions| :: versions[i] > queryVersion)
}

lemma SubVersionsLemma(versions: seq<int>, subVersions: seq<int>, v: int)
  requires |versions| > 0
  requires subSequence(subVersions, versions)
  requires Sorted(versions) && Sorted(subVersions)
  requires v > versions[|versions| - 1]
  ensures |subVersions| > 0 ==> subVersions[|subVersions| - 1] in versions 
  ensures |subVersions| > 0 ==> v > subVersions[|subVersions| - 1]
  ensures Sorted(subVersions + [v])
  ensures Sorted(versions + [v])
  {}

predicate subSequence(seq1: seq<int>, seq2: seq<int>)
  {forall v <- seq1 :: v in seq2}

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

  ghost predicate isBST(version: int)  
    reads Repr
    requires ReprProp() && BasicProp() 
  {
    if (version < ValueSetsVersions[0]) then
     true
    else
      var v := ValueAt(version);
      // var r := RightAt(version);
      // var l := LeftAt(version);
      (forall v' <- RightValueSetAt(version) :: v' > v)
      && (forall v' <- LeftValueSetAt(version) :: v' < v)
  }

  ghost predicate BinarySearchProp()
    reads Repr
    requires ReprProp() && BasicProp() 
  {
    (forall v | v >= ValueSetsVersions[0] :: isBST(v))
    && (forall v <- lefts + rights | v != null :: v.BinarySearchProp())
  }

  ghost predicate ReprProp()
    reads this, Repr
  {
    && this in Repr
    && (forall v <- lefts + rights | v != null ::
        v in Repr && this !in v.Repr && v.Repr < Repr && v.ReprProp())
    && (forall r <- rights, l <- lefts | r != null && l != null :: 
        l != r && l.Repr !! r.Repr) 
    && (forall t <- Repr ::
        t == this ||
        (exists node <- lefts + rights :: node != null && t in node.Repr))
  }

  ghost predicate BasicProp()
    reads Repr
    requires ReprProp()
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
    && Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
    && (forall v <- lefts + rights | v != null :: v.BasicProp())
  }

  ghost predicate ValueSetUnions(v: int)
    reads Repr
    requires ReprProp() && BasicProp() && VersionsProp() 
  {
    ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v)
  }

  ghost predicate ValueSetProp()
    reads Repr
    requires ReprProp() && BasicProp() && VersionsProp() 
  {
    // COMMENT: using forall v | ValueSetsVersions[0] <= v <= ValueSetsVersions[|ValueSetsVersions| - 1] did not work
    (forall v | ValueSetsVersions[0] <= v :: ValueSetUnions(v))
    && (forall v <- lefts + rights | v != null :: v.ValueSetProp())
  }

  ghost predicate VersionsProp()
    reads Repr
    requires ReprProp() 
  {
    && (forall v <- ValueSetsVersions ::
        v in valuesVersions 
        || (exists node <- lefts + rights :: node != null && v in node.ValueSetsVersions))
    && subSequence(valuesVersions, ValueSetsVersions)
    && subSequence(leftsVersions, ValueSetsVersions)
    && subSequence(rightsVersions, ValueSetsVersions)
    && (forall node <- lefts + rights | node != null :: subSequence(node.ValueSetsVersions, ValueSetsVersions))
    && (forall v <- lefts + rights | v != null :: v.VersionsProp())
  }

  ghost predicate Valid()
    reads this, Repr
  {
    ReprProp() && BasicProp() && VersionsProp() && ValueSetProp() && BinarySearchProp()
  }

  ghost function LeftValueSetAt(version: int) : (res: set<int>)
    reads Repr
    requires ReprProp() && BasicProp() 
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
    reads Repr
    requires ReprProp() && BasicProp() 
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
    ensures ReprProp() && BasicProp() && VersionsProp() && ValueSetProp() && BinarySearchProp()
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

  ghost predicate NewNodeValid(t: Node, version: int, value: int)
    reads t, t.Repr
    requires version >= 0
  {
    t.Valid()
    && t.ValueSetsVersions == [version]
    // && t.ValueSetAt(version) == {value}
    && t.ValueSets == [{value}]
    && t.valuesVersions == [version]
    && t.values == [value]
    && t.Repr == {t}
    && t.lefts == []
    && t.rights == []
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
    ensures index == -1 || IsMaxMinVersionIndex(version, index, ValueSetsVersions)
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
    ensures |ValueSetsVersions| > 0 && version >= ValueSetsVersions[0] <==> VersionIndexForValueSets(version) >= 0
    ensures VersionIndexForValueSets(version) >= 0 ==> 
            |ValueSets| > 0 && res == ValueSets[VersionIndexForValueSets(version)]
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
    ensures index == -1 || IsMaxMinVersionIndex(version, index, valuesVersions)
    ensures index == VersionIndex(version, valuesVersions)
    ensures |valuesVersions| > 0 && version >= valuesVersions[|valuesVersions| - 1] ==> index == |valuesVersions| - 1
    // ensures index == -1 || valuesVersions[index] in ValueSetsVersions
    // ensures index <= VersionIndexForValueSets(version)
  {
    VersionIndex(version, valuesVersions)
  }

  function {:opaque} ValueAt(version: int): (res: int)
    reads this
    requires Sorted(valuesVersions) && |valuesVersions| == |values|
    ensures |valuesVersions| > 0 && version >= valuesVersions[0] <==> 
            VersionIndexForValues(version) >= 0
    ensures VersionIndexForValues(version) >= 0 ==> 
            |values| > 0 && res == values[VersionIndexForValues(version)]
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
    ensures |rightsVersions| > 0 && version < rightsVersions[0] ==> index == -1
    ensures index >= 0 <==> |rightsVersions| > 0 && rightsVersions[0] <= version
    ensures index == -1 || IsMaxMinVersionIndex(version, index, rightsVersions)
    ensures index == VersionIndex(version, rightsVersions)
    // ensures |rightsVersions| == 0 ==> index == -1
    // ensures index == -1 || rightsVersions[index] in ValueSetsVersions
    // ensures index <= VersionIndexForValueSets(version)
  {
    VersionIndex(version, rightsVersions)
  }

  function {:opaque} RightAt(version: int) : (res: Node?)
    reads Repr
    requires ReprProp() && BasicProp()
    ensures res == null || (res in rights && res.BasicProp())
    ensures |rightsVersions| > 0 && version >= rightsVersions[0] <==> VersionIndexForRights(version) >= 0
    ensures VersionIndexForRights(version) >= 0 ==> 
            |rights| > 0 && res == rights[VersionIndexForRights(version)]
    ensures VersionIndexForRights(version) == -1 ==> res == null
    ensures |rightsVersions| > 0 && version >= rightsVersions[|rightsVersions| - 1] ==> res == Right()
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
    ensures index == -1 || IsMaxMinVersionIndex(version, index, leftsVersions)
    ensures index == VersionIndex(version, leftsVersions)
    // ensures index == -1 || leftsVersions[index] in ValueSetsVersions
    // ensures index <= VersionIndexForValueSets(version)
  {
    VersionIndex(version, leftsVersions)
  }

  function {:opaque} LeftAt(version: int) : (res: Node?)
    reads Repr
    requires ReprProp() && BasicProp()
    ensures res == null || (res in lefts && res.BasicProp())
    ensures |leftsVersions| > 0 && version >= leftsVersions[0] <==> VersionIndexForLefts(version) >= 0
    ensures VersionIndexForLefts(version) >= 0 ==> 
            |lefts| > 0 && res == lefts[VersionIndexForLefts(version)]
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
    requires ReprProp() && BasicProp() && VersionsProp() && ValueSetProp() && BinarySearchProp()
    // requires version >= ValueSetsVersions[0]
    ensures res <==> value in ValueSetAt(version)
  {
    if (version < valuesVersions[0]) then
      false
    else
      var i := VersionIndexForValues(version);
      if i == -1 then
        assert VersionIndexForValueSets(version) == -1;
        assert value !in ValueSetAt(version);
        false
      else
        assert version >= valuesVersions[0];
        assert isBST(version);  // COMMENT: trigger
        assert ValueSetUnions(version); // COMMENT: trigger
        var x := ValueAt(version);
        if x > value then
          var left := LeftAt(version);
          assert value !in RightValueSetAt(version);
          if left == null then 
            false
          else
            left.Find(version, value)
        else if x < value then
          var right := RightAt(version);
          assert value !in LeftValueSetAt(version);
          if right == null then
            false
          else
            right.Find(version, value)
        else
          true
  }

  lemma VersionsLemma2(version: int, versions1: seq<int>, versions2: seq<int>)
    requires versions1 < versions2
    requires |versions2| == 0 || version < versions2[|versions1|]
    requires Sorted(versions1) && Sorted(versions2)
    ensures VersionIndex(version, versions1) == VersionIndex(version, versions2)
  {}

  // twostate predicate LeftBranchUnchanged()
  //   reads this, Repr
  //   requires old(Repr) <= Repr
  //   requires old(ReprProp()) && old(BasicProp()) 
  //   // ensures old(lefts) == lefts
  //   // ensures forall l <- old(lefts) | l != null :: l in old(Repr)
  //   // ensures forall l <- lefts | l != null :: l in old(Repr)
  // {
  //   old(values) == values
  //   && old(valuesVersions) == valuesVersions
  //   && old(lefts) == lefts
  //   && old(leftsVersions) == leftsVersions
  //   && (forall l <- lefts | l != null :: 
  //         l.ValueSets == old(l.ValueSets)
  //         && l.ValueSetsVersions == old(l.ValueSetsVersions)
  //         && old(l.Repr) == l.Repr
  //         // && l.LeftBranchUnchanged()
  //         )
  // }

  // twostate lemma RightInsert(t: Node, new newNode: Node, version: int, value: int)
  //   requires old(t.ReprProp()) && old(t.BasicProp()) && old(t.VersionsProp()) && old(t.ValueSetProp()) && old(t.BinarySearchProp())
  //   requires version > old(t.ValueSetsVersions[|t.ValueSetsVersions| - 1])
  //   // unchanged part
  //   requires old(t.lefts) == t.lefts
  //   requires forall l <- t.lefts | l != null :: old(l.Repr) == l.Repr
  //   requires forall r <- old(t.rights) | r != null :: 
  //             r.ValueSets == old(r.ValueSets) && r.ValueSetsVersions == old(r.ValueSetsVersions)
  //   // changed part
  //   requires NewNodeValid(newNode, version, value)
  //   requires old(t.Repr) + {newNode} == t.Repr
  //   requires t.rights == old(t.rights) + [newNode]
  //   requires t.rightsVersions == old(t.rightsVersions) + [version]
  //   requires t.ValueSets == old(t.ValueSets) + [old(t.ValueSet()) + {value}]
  //   requires t.ValueSetsVersions == old(t.ValueSetsVersions) + [version]
  //   ensures t.ReprProp() && t.BasicProp() && t.VersionsProp() && t.ValueSetProp() && t.BinarySearchProp() 
  // {
  //   assert Sorted(newNode.ValueSetsVersions);
  //   assert version > old(t.ValueSetsVersions[|t.ValueSetsVersions| - 1]);
  //   SubVersionsLemma(old(t.ValueSetsVersions), old(t.rightsVersions), version);
  //   SubVersionsLemma(old(t.ValueSetsVersions), old(t.valuesVersions), version);
  //   assert Sorted(t.ValueSetsVersions);
  //   assert Sorted(t.rightsVersions);

  //   assert t.ReprProp();

  //   assume false;

  //   assert t.BasicProp();
  //   assert old(t.ReprProp());
  //   // assert old(NodesBasicPop(t.lefts));
  //   assert forall v <- old(t.lefts) | v != null :: old(v.BasicProp());
  //   assert old(t.lefts) == t.lefts;
  //   assert forall v <- t.lefts | v != null :: v.BasicProp();
  //   // assert NodesBasicPop(t.lefts);

  //   assume false;

  //   // assert NodesBasicPop(t.rights);

    

  //   assert t.VersionsProp() by {
  //     assert old(t.PartOfValueSetsVersions1(t.rightsVersions));
  //       assert version in t.rightsVersions && version in t.ValueSetsVersions;
  //   } 

  //   assert forall v | v >= t.ValueSetsVersions[0] :: t.ValueAt(v) == old(t.ValueAt(v));
  //   assume forall v | v >= t.ValueSetsVersions[0] :: t.LeftValueSetAt(v) == old(t.LeftValueSetAt(v));
  //   assume forall v | v >= version :: 
  //         && old(t.RightValueSetAt(v)) == {} 
  //         && t.RightValueSetAt(v) == {value};

  //   forall v | version > v >= t.ValueSetsVersions[0] ensures t.ValueSetAt(v) == old(t.ValueSetAt(v)) {
  //     VersionsLemma2(v, old(t.ValueSetsVersions), t.ValueSetsVersions);
  //   }

  //   if (old(|t.rightsVersions| > 0)) {
  //     assert version > old(t.rightsVersions[|t.rightsVersions| - 1]);
  //   }

  //   forall v | version > v >= t.ValueSetsVersions[0] ensures t.RightAt(v) == old(t.RightAt(v)) {
  //     VersionsLemma2(v, old(t.rightsVersions), t.rightsVersions);
  //     assert t.VersionIndexForRights(v) == old(t.VersionIndexForRights(v));
  //     assert t.RightAt(v) == old(t.RightAt(v));
  //     assert t.RightValueSetAt(v) == old(t.RightValueSetAt(v));
  //   }

  //   assert t.ValueSetProp() by {
  //     forall v | v >= t.ValueSetsVersions[0] ensures t.ValueSetUnions(v) {
  //       assert old(t.ValueSetUnions(v));
  //       assert old(t.ValueSetAt(v)) == {old(t.ValueAt(v))} + old(t.LeftValueSetAt(v)) + old(t.RightValueSetAt(v));

  //       if (v >= version) {
  //         assert t.ValueSetAt(v) == old(t.ValueSetAt(v)) + {value};
  //         assert old(t.RightValueSetAt(v)) == {};
  //         assert t.RightValueSetAt(v) == {value};
  //         assert t.ValueSetAt(v) == {t.ValueAt(v)} + t.LeftValueSetAt(v) + t.RightValueSetAt(v);
  //       }
  //     }
  //   }

  //   // BinarySearchProp()
  //   forall v | v >= t.ValueSetsVersions[0] ensures t.isBST(v) {
  //     assert old(t.isBST(v));
  //     if (v >= version) {
  //       assume false;
  //       assert old(t.RightValueSetAt(v)) == {};
  //       assert t.RightValueSetAt(v) == {value};
  //       assert old(t.LeftValueSetAt(v)) == t.LeftValueSetAt(v);
  //     } else {
  //       assume false;
  //     }
  //   }
  // }

  method Insert(version: int, value: int) returns (res: Node?) 
    modifies Repr
    decreases Repr
    requires ReprProp() && BasicProp() && VersionsProp() && ValueSetProp() && BinarySearchProp()
    requires version > ValueSetsVersions[|ValueSetsVersions| - 1]
    ensures res != null ==> 
      fresh(res) && Repr == old(Repr) + {res} && NewNodeValid(res, version, value)
    ensures res == null ==> 
      Repr == old(Repr) 
      && lefts == old(lefts) && leftsVersions == old(leftsVersions)
      && rights == old(rights)
      && values == old(values) && ValueSets == old(ValueSets)
    ensures res != null <==> value !in ValueSet()
    ensures Valid()
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

    // ensures res == null <==> Repr == old(Repr) && ValueSets == old(ValueSets) && value in old(ValueSetAt(version))
    // ensures value in ValueSetAt(version) 
  {
    var x := Value();
    var right := Right();
    var left := Left();
    var valueSet := ValueSet();

    assume false;
    
    assert right != null ==> right.Valid();
    assert left != null ==> left.Valid();
    
    label L:

    if x > value {
      assume false;
      if left == null { 
        assume false;
        res := new Node.Init(version, value);
        lefts := lefts + [res];
        leftsVersions := leftsVersions + [version];
      } else {
        SubVersionsLemma(ValueSetsVersions, left.ValueSetsVersions, version);
        res := left.Insert(version, value);
      }
    } else if x < value {
      if right == null {
        res := new Node.Init(version, value);        
        rights := rights + [res];
        rightsVersions := rightsVersions + [version];

        Repr := Repr + right.Repr;
        if (res != null) {
            ValueSets := ValueSets + [valueSet + {value}];
            ValueSetsVersions := ValueSetsVersions + [version];
        }
                
        // Repr := Repr + {res};
        // ValueSets := ValueSets + [ValueSet() + {value}];
        // ValueSetsVersions := ValueSetsVersions + [version];

        // assert lefts == old@L(lefts);

        // assert ReprProp();
        // assert BasicProp() by {
        //   assert old@L(BasicProp());
        //   assert leftsVersions == old@L(leftsVersions);
        //   SubVersionsLemma(old@L(ValueSetsVersions), old@L(rightsVersions), version);
        //   assert |rights| == |rightsVersions|;
        //   assert Sorted(rightsVersions);
        //   assert Sorted(ValueSetsVersions);
        // }

        // forall v | v >= ValueSetsVersions[0] ensures ValueAt(v) == old@L(ValueAt(v)) {
        //   assert valuesVersions == old@L(valuesVersions);
        //   assert values == old@L(values);
        //   assert VersionIndexForValues(v) == old@L(VersionIndexForValues(v));
        // }

        // forall v | v >= ValueSetsVersions[0] ensures LeftAt(v) == old@L(LeftAt(v)) && LeftValueSetAt(v) == old@L(LeftValueSetAt(v)) {
        //   assert leftsVersions == old@L(leftsVersions);
        //   assert VersionIndexForLefts(v) == old@L(VersionIndexForLefts(v));
        //   assert LeftAt(v) == old@L(LeftAt(v));
        //   if (LeftAt(v) != null) {
        //     assert LeftAt(v).ValueSetsVersions == old@L(LeftAt(v).ValueSetsVersions);
        //     // assert LeftAt(v).ValueSetAt(v) == old@L(LeftAt(v).ValueSetAt(v));
        //   }
        // }

        // assert {:split_here} VersionsProp() by {
        //   assert old@L(VersionsProp());
        //   assert valuesVersions == old@L(valuesVersions);
        //   assert ValueSetsVersions == old@L(ValueSetsVersions) + [version];
        //   assert (forall v <- ValueSetsVersions ::
        //                 v in valuesVersions 
        //                 || (exists node <- lefts + rights :: node != null && v in node.ValueSetsVersions));
        //   assert subSequence(valuesVersions, ValueSetsVersions);
        //   assert leftsVersions == old@L(leftsVersions);
        //   assert subSequence(leftsVersions, ValueSetsVersions);
        //   assert subSequence(rightsVersions, ValueSetsVersions);

        //   assert subSequence(res.ValueSetsVersions, ValueSetsVersions);
          
        //   assert rights == old@L(rights) + [res];
        //   assert (forall node <- lefts + rights | node != null :: subSequence(node.ValueSetsVersions, ValueSetsVersions));
        //   assert res.VersionsProp();
        //   assert forall v <- lefts + rights | v != null && v != res :: v.VersionsProp();
        //   assert (forall v <- lefts + rights | v != null :: v.VersionsProp());
        // }

    //     assume false;

    //     assert ValueSetProp() by {
    //       assert forall v <- lefts + rights | v != null :: v.ValueSetProp();
    //     }

    //     assume false;

    //     assert BinarySearchProp() by {
    //       assert old@L(BinarySearchProp());

    //       assume false;

    //       assert rights == old@L(rights) + [res];
    //       assert rightsVersions == old@L(rightsVersions) + [version];

    //       forall v | v >= ValueSetsVersions[0] ensures isBST(v) {
    //         assert old@L(isBST(v));
    //         if (v < version) {
    //           assert isBST(v) by {
    //             assert RightAt(v) == old@L(RightAt(v)) by {
    //               VersionsLemma2(v, old@L(rightsVersions), rightsVersions);
    //               assert VersionIndexForRights(v) == old@L(VersionIndexForRights(v));
    //             }
    //             assert ValueAt(v) == old@L(ValueAt(v)) by {

    //             }
    //             // VersionsLemma2(v, old@L(ValueSetsVersions), ValueSetsVersions);
    //             if (RightAt(v) != null) {
    //               assert forall r <- rights | r != null && r != res :: r.ValueSetsVersions == old@L(r.ValueSetsVersions);
    //               assert RightAt(v).ValueSetAt(v) == old@L(RightAt(v).ValueSetAt(v));
    //             }
    //             assert LeftAt(v) == old@L(LeftAt(v));
    //             if (LeftAt(v) != null) {
    //               assert LeftAt(v).ValueSetAt(v) == old@L(LeftAt(v).ValueSetAt(v));
    //             }
                
    //           }
    //         } else {
    //           assume isBST(v);
    //         }
            
    //                   // (r != null ==> (forall v' <- r.ValueSetAt(version) :: v' > v) && r.isBST(version))
    //   // && (l != null ==> (forall v' <- l.ValueSetAt(version) :: v' < v) && l.isBST(version))
    //       }

    //       assert forall v <- lefts + rights | v != null && v != res :: v.BinarySearchProp();
    //       assume (forall v <- lefts + rights | v != null :: v.BinarySearchProp());
    //     }
        

      } else {
        assume false;
        SubVersionsLemma(ValueSetsVersions, right.ValueSetsVersions, version);
        res := right.Insert(version, value);
        assert rights == old@L(rights);
        assert rightsVersions == old@L(rightsVersions);

        Repr := Repr + right.Repr;
        if (res != null) {
            ValueSets := ValueSets + [valueSet + {value}];
            ValueSetsVersions := ValueSetsVersions + [version];
        }
        // if (res != null) {
        //   assume false;
        //   assert Sorted(rightsVersions);
        // //   Repr := Repr + {res};
        // //   ValueSets := ValueSets + [ValueSet() + {value}];
        // //   ValueSetsVersions := ValueSetsVersions + [version];
        //   assert Sorted(ValueSetsVersions);
        //   assert valuesVersions == old(valuesVersions);
        //   assert values == old(values);

        //   // RightInsert(this, res, version, value);
        // } 
      }
    } else {
      // COMMENT: comment out the "assume false" below increases the verification time from 13s to 35s
      res := null;
    }


  }
}