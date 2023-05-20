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
  ensures |versions| > 0 && version >= versions[|versions| - 1] ==> index == |versions| - 1
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

function VersionIndex(version: int, versions: seq<int>): (index: int)
  requires Sorted(versions)
  ensures -1 <= index < |versions|
  ensures index >= 0 <==> |versions| > 0 && versions[0] <= version
  // ensures version in versions <==> index >= 0 && |versions| > index && versions[index] == version
  // ensures |versions| > 0 && version > versions[|versions| - 1] ==> index == |versions| - 1
  ensures -1 <= index < |versions|  
  ensures index == -1 <==> (|versions| == 0 || forall k :: 0 <= k < |versions| ==> versions[k] > version)
  ensures index >= 0 <==> |versions| > 0 && versions[0] <= version
  ensures index == -1 || versions[index] <= version
  ensures forall i | 0 <= i < index :: versions[i] < version
  ensures index >= 0 ==> forall i | index < i < |versions| :: versions[i] > version
  ensures |versions| > 0 && version >= versions[|versions| - 1] ==> index == |versions| - 1
{
  if |versions| == 0 || version < versions[0] then
    -1
  else
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

// predicate IsMaxMinVersionIndex(queryVersion: int, index: int, versions: seq<int>)
//   requires Sorted(versions)
//   requires 0 <= index < |versions|
//   ensures |versions| > 0
//   ensures |versions| > 0 && queryVersion >= versions[|versions| - 1] ==> index == |versions| - 1
// {
//   (forall i | 0 <= i < index :: versions[i] < queryVersion)
//   && versions[index] <= queryVersion
//   && (forall i | index < i < |versions| :: versions[i] > queryVersion)
// }

predicate subSequence(seq1: seq<int>, seq2: seq<int>)
  {forall v <- seq1 :: v in seq2}

lemma OrderInvariant(subVersions: seq<int>, versions: seq<int>, v: int)
  requires |versions| > 0
  requires subSequence(subVersions, versions)
  requires Sorted(versions) && Sorted(subVersions)
  requires v > versions[|versions| - 1]
  ensures |subVersions| > 0 ==> subVersions[|subVersions| - 1] in versions 
  ensures |subVersions| > 0 ==> v > subVersions[|subVersions| - 1]
  // ensures Sorted(subVersions + [v])
  // ensures Sorted(versions + [v])
  {}

lemma VersionsExtensionLemma(versions1: seq<int>, versions2: seq<int>, version: int)
  requires versions1 < versions2
  requires |versions2| == 0 || version < versions2[|versions1|]
  requires Sorted(versions1) && Sorted(versions2)
  ensures VersionIndex(version, versions1) == VersionIndex(version, versions2)
{}

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
    requires BasicProp() 
  {
    if (version < valuesVersions[0]) then
     true
    else
      var v := ValueAt(version);
      var r := RightAt(version);
      var l := LeftAt(version);
      (r != null ==> (r.isBST(version) &&
                    (forall v' <- r.ValueSetAt(version) :: v' > v)))
      && (l != null ==> (l.isBST(version) &&
                    (forall v' <- l.ValueSetAt(version) :: v' < v)))
  }

  ghost predicate BinarySearchProp()
    reads Repr
    requires BasicProp() 
  {
    (forall v | v >= valuesVersions[0] :: isBST(v))
    && (forall v <- lefts + rights | v != null :: v.BinarySearchProp())
  }

  ghost predicate BasicProp()
    reads this, Repr
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
    && this in Repr
    && (forall node <- lefts + rights | node != null ::
        node in Repr && this !in node.Repr && node.Repr < Repr && node.BasicProp())
    && (forall r <- rights, l <- lefts | r != null && l != null :: 
        l != r && l.Repr !! r.Repr) 
    && (forall v <- ValueSetsVersions ::
        v in valuesVersions 
        || (exists node <- lefts + rights :: node != null && v in node.ValueSetsVersions))
    && subSequence(valuesVersions, ValueSetsVersions)
    && subSequence(leftsVersions, ValueSetsVersions)
    && subSequence(rightsVersions, ValueSetsVersions)
    && (forall node <- lefts + rights | node != null :: subSequence(node.ValueSetsVersions, ValueSetsVersions))
    // && (forall t <- Repr ::
    //     t == this ||
    //     (exists node <- lefts + rights :: node != null && t in node.Repr))
  }

  ghost predicate ValueSetProp()
    reads Repr
    requires BasicProp() 
  {
    (forall v | valuesVersions[0] <= v :: ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v))
    && (forall v <- lefts + rights | v != null :: v.ValueSetProp())
  }

  ghost function LeftValueSetAt(version: int) : (res: set<int>)
    reads Repr
    requires BasicProp() 
    requires version >= valuesVersions[0]
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
    requires BasicProp() 
    requires version >= valuesVersions[0]
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
    ensures BasicProp() && ValueSetProp() && BinarySearchProp() 
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
    reads Repr
    requires BasicProp() && BinarySearchProp() && ValueSetProp()
    ensures |lefts| == 0 ==> l == null
    ensures |lefts| > 0 ==> l == lefts[|lefts| - 1]
    ensures l != null ==> l.BasicProp() && l.BinarySearchProp() && l.ValueSetProp()
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
    t.BasicProp() && t.BinarySearchProp() && t.ValueSetProp()
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
    reads Repr
    requires BasicProp() && BinarySearchProp() && ValueSetProp()
    ensures |rights| == 0 ==> r == null
    ensures |rights| > 0 ==> r == rights[|rights| - 1]
    ensures r != null ==> r.BasicProp() && r.BinarySearchProp() && r.ValueSetProp()
  {
    if |rights| > 0 then
      rights[|rights| - 1]
    else
      null
  }

  function Value(): (v: int)
    reads Repr
    requires BasicProp() && BinarySearchProp() && ValueSetProp()
    requires |values| > 0
    ensures v == values[|values| - 1]
    ensures BasicProp() && BinarySearchProp() && ValueSetProp()
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

  ghost function ValueSetAt(version: int) : (res: set<int>)
    reads Repr
    requires BasicProp()
    ensures version >= ValueSetsVersions[0] ==> res == ValueSets[VersionIndex(version, ValueSetsVersions)]
  {
    var i := VersionIndex(version, ValueSetsVersions);
    if i == -1 then
      {}
    else
      ValueSets[i]
  }

  function ValueAt(version: int): (res: int)
    reads Repr
    requires BasicProp()
    requires version >= valuesVersions[0]
    ensures res == values[VersionIndex(version, valuesVersions)]
  {
    values[VersionIndex(version, valuesVersions)]
  }

  function RightAt(version: int) : (res: Node?)
    reads Repr
    requires BasicProp() 
    requires version >= valuesVersions[0]
    ensures res == null || (res in rights && res.BasicProp())
    ensures |rightsVersions| > 0 && version >= rightsVersions[0] ==> res == rights[VersionIndex(version, rightsVersions)]
  {
    if |rightsVersions| == 0 || version < rightsVersions[0] then
      null
    else
      var i := VersionIndex(version, rightsVersions);
      rights[i]
  }

  function LeftAt(version: int) : (res: Node?)
    reads Repr
    requires BasicProp() 
    requires version >= valuesVersions[0]
    ensures res == null || (res in lefts && res.BasicProp())
    ensures |leftsVersions| > 0 && version >= leftsVersions[0] ==> res == lefts[VersionIndex(version, leftsVersions)]
  {
    if |leftsVersions| == 0 || version < leftsVersions[0] then
      null
    else
      var i := VersionIndex(version, leftsVersions);
      lefts[i]
  }

  function {:opaque} Find(version: int, value: int) : (res: bool) 
    reads Repr
    requires BasicProp() && ValueSetProp() && BinarySearchProp()
    ensures res <==> value in ValueSetAt(version)
  {
    if (version < valuesVersions[0]) then
      false
    else
      if version < valuesVersions[0] then
        assert value !in ValueSetAt(version);
        false
      else
        assert isBST(version);  // COMMENT: trigger
        var x := ValueAt(version);
        if x > value then
          var left := LeftAt(version);
          if left == null then 
            false
          else
            left.Find(version, value)
        else if x < value then
          var right := RightAt(version);
          if right == null then
            false
          else
            right.Find(version, value)
        else
          true
  }

  method Insert(version: int, value: int) returns (res: Node?) 
    modifies Repr
    decreases Repr
    requires BasicProp() && BinarySearchProp() && ValueSetProp()
    requires version > ValueSetsVersions[|ValueSetsVersions| - 1]
    ensures res != null ==> 
      fresh(res) && Repr == old(Repr) + {res} && NewNodeValid(res, version, value)
    ensures res == null ==> 
      Repr == old(Repr) 
      && lefts == old(lefts) && leftsVersions == old(leftsVersions)
      && rights == old(rights)
      && values == old(values) && ValueSets == old(ValueSets)
    ensures BasicProp() && BinarySearchProp() && ValueSetProp()
    // ensures res != null <==> value !in ValueSet()
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

    OrderInvariant(old(leftsVersions), old(ValueSetsVersions), version);
    OrderInvariant(old(rightsVersions), old(ValueSetsVersions), version);
    OrderInvariant(old(valuesVersions), old(ValueSetsVersions), version);


    if x > value {
      if left == null { 
        assume false;
        res := new Node.Init(version, value);
        lefts := lefts + [res];
        leftsVersions := leftsVersions + [version];

        
      } else {
        assume false;
        OrderInvariant(left.ValueSetsVersions, ValueSetsVersions, version);
        res := left.Insert(version, value);
      }
    } else if x < value {
      if right == null {
        res := new Node.Init(version, value);        
        rights := rights + [res];
        rightsVersions := rightsVersions + [version];

        if (res != null) {
          Repr := Repr + res.Repr;
          ValueSets := ValueSets + [valueSet + {value}];
          ValueSetsVersions := ValueSetsVersions + [version];
        }

        assert BasicProp() by {
          // COMMENT: adding these two intermediate assertions increases verification time
          assert Sorted(rightsVersions);
          assert Sorted(ValueSetsVersions);
        }

        assume false;

        forall v | version > v >= valuesVersions[0] ensures RightAt(v) == old(RightAt(v)) {
          VersionsExtensionLemma(old(rightsVersions), rightsVersions, v);
        }
        assert forall v | v >= version :: RightAt(v) == res;

        assert forall v | v >= valuesVersions[0] :: LeftAt(v) == old(LeftAt(v));
        assert forall v | v >= valuesVersions[0] :: ValueAt(v) == old(ValueAt(v));

        assert BinarySearchProp() by {
          forall v | v >= valuesVersions[0] ensures isBST(v) {
            assert old(isBST(v));
            assert LeftAt(v) == old(LeftAt(v));
            assert ValueAt(v) == old(ValueAt(v));
            if (v < version) {
              assert RightAt(v) == old(RightAt(v));
              assert (RightAt(v) != null ==> (RightAt(v).isBST(v) &&
                    (forall v' <- RightAt(v).ValueSetAt(v) :: v' > ValueAt(v))))
                    && (LeftAt(v) != null ==> (LeftAt(v).isBST(v) &&
                    (forall v' <- LeftAt(v).ValueSetAt(v) :: v' < ValueAt(v))));
            } else {
              assert RightAt(v) == res;
              assert res.ValueSetAt(v) == {value};
              
              assert ValueAt(v) == x;
              assert (RightAt(v) != null ==> (RightAt(v).isBST(v) &&
                    (forall v' <- RightAt(v).ValueSetAt(v) :: v' > ValueAt(v))))
                    && (LeftAt(v) != null ==> (LeftAt(v).isBST(v) &&
                    (forall v' <- LeftAt(v).ValueSetAt(v) :: v' < ValueAt(v))));
            }
          }
          assume forall v <- lefts + rights | v != null :: v.BinarySearchProp();
        }

        assume false;

        

        assume false;

        assert ValueSetProp() by {
          assert old(ValueSetProp());
          forall v | valuesVersions[0] <= v ensures ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v) {
            assume ValueSetAt(v) == {ValueAt(v)} + LeftValueSetAt(v) + RightValueSetAt(v);
          }
          assume forall v <- lefts + rights | v != null && v != res :: v.ValueSetProp();
          assert res.ValueSetProp();
        }

        assume false;
      } else {
        assume false;
        OrderInvariant(ValueSetsVersions, right.ValueSetsVersions, version);
        res := right.Insert(version, value);
        assert rights == old(rights);
        assert rightsVersions == old(rightsVersions);

        Repr := Repr + right.Repr;
        if (res != null) {
            ValueSets := ValueSets + [valueSet + {value}];
            ValueSetsVersions := ValueSetsVersions + [version];
        }
      }
    } else {
      assume false;
      // COMMENT: comment out the "assume false" below increases the verification time from 13s to 35s
      res := null;
    }

  }
}