// class Entry {
//   ghost var Repr: set<Node>
//   ghost var ValueSets: seq<(int, set<int>)> 

//   var roots: seq<Node?>
//   var time: int

//   predicate Valid()
//     reads this, Repr
//   {
//     time >= 0 && |roots| > 0 &&
//     (forall r :: r in roots && r != null ==> r in Repr && Repr >= r.Repr && r.Valid()) // it is a bit weird not being able to write only "Repr >= r.Repr && r.Valid()""
//   }

//   constructor Init()
//     ensures Valid()
//   {
//     roots := [null];
//     time := 0;
//     Repr := {};
//   }
  
//   // method Insert(value: int)
//   //   requires Valid()
//   //   modifies this, Repr
//   //   ensures Valid()
//   // {
//   //   time := time + 1;
//   //   var root := roots[|roots| - 1];
//   //   if root == null {
//   //     var node := new Node.Init(time, value);
//   //     roots := roots + [node];
//   //     Repr := Repr + {node};
//   //     assert Repr >= node.Repr;
//   //   } else {
//   //     var newNode := root.Insert(time, value);
//   //     roots := roots + [root];
//   //     Repr := Repr + {newNode} + newNode.Repr;
//   //     assert Repr >= newNode.Repr;
//   //   }
//   // }
// }

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

  // Consistently use A && B ==> C when I wrote A ==> B ==> C
  ghost predicate Valid() 
    reads this, Repr
  {
    |values| == |valuesVersions|
    && |lefts| == |leftsVersions|
    && |rights| == |rightsVersions|
    && |ValueSetsVersions| == |ValueSets|
    && |ValueSetsVersions| >= |valuesVersions| + |rightsVersions| + |leftsVersions| // Different performance if written as && |ValueSets| >= |values| + |rights| + |lefts|
    && Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
    && |values| > 0 
    && |ValueSets| > 0
    && this in Repr
    && (forall l <- lefts | l != null ::
        l in Repr && this !in l.Repr && l.Repr < Repr && l.Valid()) 
    && (forall r <- rights | r != null ::
        r in Repr && this !in r.Repr && r.Repr < Repr && r.Valid()) 
    // the two strong assumption does not hold for fat node method in general
    && (forall l1 <- lefts, l2 <- lefts | l1 != null && l2 != null && l1 != l2 ::
        l1.Repr !! l2.Repr)
    && (forall r1 <- rights, r2 <- rights | r1 != null && r2 != null && r1 != r2 ::
        r1.Repr !! r2.Repr)
    && (forall r <- rights, l <- lefts | r != null && l != null :: 
        l != r && l.Repr !! r.Repr) 
    && (forall node <- Repr :: 
          (node == this)
          || (exists l | l in lefts && l != null :: node in l.Repr)
          || (exists r | r in rights && r != null :: node in r.Repr))
    && (forall rv <- rightsVersions, lv <- leftsVersions :: rv != lv)
    // binary search tree property
    && (forall l <- lefts | l != null ::
          forall ls <- l.ValueSets, lv <- ls, v <- values :: lv < v)
    && (forall r <- rights | r != null ::
          forall rs <- r.ValueSets, rv <- rs, v <- values :: rv > v)
    // all timestmps are larger than created
    && (|leftsVersions| > 0 ==> leftsVersions[0] >= 0) 
    && (|rightsVersions| > 0 ==> rightsVersions[0] >= 0) 
    && (valuesVersions[0] >= 0) 
    && (ValueSetsVersions[0] == valuesVersions[0])
    // values and ValueSets
    && (forall i | 0 <= i < |valuesVersions| ::
          exists j | i <= j < |ValueSetsVersions| ::
            valuesVersions[i] == ValueSetsVersions[j])
    && (forall i | 0 <= i < |leftsVersions| ::
          exists j | i <= j < |ValueSetsVersions| ::
            leftsVersions[i] == ValueSetsVersions[j])
    && (forall i | 0 <= i < |rightsVersions| ::
          exists j | i <= j < |ValueSetsVersions| ::
            rightsVersions[i] == ValueSetsVersions[j])
    && (forall i | 0 <= i < |ValueSetsVersions| ::
          ((exists j | 0 <= j <= i < |valuesVersions| :: valuesVersions[j] == ValueSetsVersions[i])
          || (exists j | 0 <= j <= i < |leftsVersions| :: leftsVersions[j] == ValueSetsVersions[i])
          || (exists j | 0 <= j <= i < |rightsVersions| :: rightsVersions[j] == ValueSetsVersions[i])))
  }

  ghost predicate ValueSetValid()
    reads Repr
    requires Valid()
  {
    // ValueSets are union of values of its own and its left and right children
    && (|lefts| == 0 && |rights| == 0 
        && |ValueSetsVersions| == |ValueSets|
        && |valuesVersions| == |values| ==>
          |ValueSets| == |values|  
          && forall i | 0 <= i < |ValueSetsVersions| ::
              valuesVersions[i] == ValueSetsVersions[i] && ValueSets[i] == {values[i]})
    && (|lefts| > 0 && |rights| == 0 
        && |ValueSetsVersions| == |ValueSets|
        && |leftsVersions| == |lefts|
        && |rightsVersions| == |rights|
        && |valuesVersions| == |values| ==>
          forall i | 0 <= i < |ValueSetsVersions| ::
            exists j, k | 0 <= j <= i < |leftsVersions| && 0 <= k <= i < |valuesVersions| ::
              IsMaxMinVersion(ValueSetsVersions[i], leftsVersions[j], leftsVersions)
              && IsMaxMinVersion(ValueSetsVersions[i], valuesVersions[k], valuesVersions)
              // && (leftsVersions[j] == ValueSetsVersions[i] || valuesVersions[k] == ValueSetsVersions[i])
              && (lefts[j] != null ==> 
                    exists x | 0 <= x < |lefts[j].ValueSetsVersions| ::
                      IsMaxMinVersion(ValueSetsVersions[i], lefts[j].ValueSetsVersions[x], lefts[j].ValueSetsVersions) 
                      && |lefts[j].ValueSetsVersions| == |lefts[j].ValueSets| // to speed up well-formedness check
                      && ValueSets[i] == {values[k]} + lefts[j].ValueSets[x])
              && (lefts[j] == null ==> ValueSets[i] == {values[k]})) 
    && (|rights| > 0 && |lefts| == 0
        && |ValueSetsVersions| == |ValueSets|
        && |leftsVersions| == |lefts|
        && |rightsVersions| == |rights|
        && |valuesVersions| == |values| ==>
          forall i | 0 <= i < |ValueSetsVersions| ::
            exists j, k | 0 <= j <= i < |rightsVersions| && 0 <= k <= i < |valuesVersions| ::
              IsMaxMinVersion(ValueSetsVersions[i], rightsVersions[j], rightsVersions)
              && IsMaxMinVersion(ValueSetsVersions[i], valuesVersions[k], valuesVersions)
              // && (rightsVersions[k] == ValueSetsVersions[i] || valuesVersions[j] == ValueSetsVersions[i])
              && (rights[j] != null ==> 
                    exists x | 0 <= x < |rights[j].ValueSetsVersions| ::
                          IsMaxMinVersion(ValueSetsVersions[i], rights[j].ValueSetsVersions[x], rights[j].ValueSetsVersions) 
                          && |rights[j].ValueSetsVersions| == |rights[j].ValueSets| // to speed up well-formedness check
                          && ValueSets[i] == {values[k]} + rights[j].ValueSets[x])
              && (rights[j] == null ==> ValueSets[i] == {values[k]})) 
    && (|rights| > 0 && |lefts| > 0
        && |ValueSetsVersions| == |ValueSets|
        && |leftsVersions| == |lefts|
        && |rightsVersions| == |rights|
        && |valuesVersions| == |values| ==>
          forall i | 0 <= i < |ValueSetsVersions| ::
            exists j, k, l | 0 <= j <= i < |values| && 0 <= k <= i < |rights| && 0 <= l <= i < |lefts| ::
              IsMaxMinVersion(ValueSetsVersions[i], valuesVersions[i], valuesVersions)
              && IsMaxMinVersion(ValueSetsVersions[i], rightsVersions[k], rightsVersions)
              && IsMaxMinVersion(ValueSetsVersions[i], leftsVersions[l], leftsVersions)
              // && (rightsVersions[k] == ValueSetsVersions[i]
              //   || leftsVersions[l] == ValueSetsVersions[i] 
              //   || valuesVersions[j] == ValueSetsVersions[i])
              && (lefts[l] != null && rights[k] != null ==> 
                    exists x, y | 0 <= x < |lefts[l].ValueSetsVersions| && 0 <= y < |rights[k].ValueSetsVersions| ::
                      IsMaxMinVersion(ValueSetsVersions[i], lefts[l].ValueSetsVersions[x], lefts[l].ValueSetsVersions)
                      && IsMaxMinVersion(ValueSetsVersions[i], rights[k].ValueSetsVersions[y], rights[k].ValueSetsVersions)
                      && |lefts[l].ValueSetsVersions| == |lefts[l].ValueSets| // to speed up well-formedness check
                      && |rights[k].ValueSetsVersions| == |rights[k].ValueSets| // to speed up well-formedness check 
                      &&  ValueSets[i] == {values[j]} + lefts[l].ValueSets[x] + rights[k].ValueSets[y])
              && (lefts[l] != null && rights[k] == null ==> 
                    exists x | 0 <= x < |lefts[l].ValueSetsVersions| ::
                      IsMaxMinVersion(ValueSetsVersions[i], lefts[l].ValueSetsVersions[x], lefts[l].ValueSetsVersions)
                      && |lefts[l].ValueSetsVersions| == |lefts[l].ValueSets| // to speed up well-formedness check
                      && ValueSets[i] == {values[j]} + lefts[l].ValueSets[x])
              && (rights[k] != null && lefts[l] == null ==> 
                    exists x | 0 <= x < |rights[k].ValueSetsVersions| ::
                      IsMaxMinVersion(ValueSetsVersions[i], rights[k].ValueSetsVersions[x], rights[k].ValueSetsVersions)
                      && |rights[k].ValueSetsVersions| == |rights[k].ValueSets| // to speed up well-formedness check 
                      &&  ValueSets[i] == {values[j]} + rights[k].ValueSets[x])
              && (rights[k] == null && lefts[l] == null ==> ValueSets[i] == {values[j]})) 
  }

  predicate Sorted(s: seq<int>) 
  {
    (forall i, j | 0 <= i < j < |s| :: 0 <= s[i] < s[j])
    && (forall i | 0 <= i < |s| :: 0 <= s[i])
  }

  predicate IsMaxMinVersion(version: int, maxMinVersion: int, versions: seq<int>)
    // requires Sorted(versions)
  {
    maxMinVersion <= version
    && (maxMinVersion == -1 
        || (maxMinVersion in versions
            && forall v <- versions :: v < maxMinVersion || v == maxMinVersion || v > version))
  }

  constructor Init(time: int, value: int)
    requires time > 0
    ensures Valid() && fresh(Repr)
    ensures lefts == []
    ensures leftsVersions == []
    ensures rights == []
    ensures rightsVersions == []
    ensures Repr == {this}
    ensures values == [value]
    ensures valuesVersions == [time]
    ensures ValueSets == [{value}]
    ensures ValueSetsVersions == [time]
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

  function {:opaque} Left(): (l: Node?)
    reads Repr 
    requires Valid()
    ensures l != null ==> l in lefts && l.Valid()
  {
    if |lefts| > 0 then
      lefts[|lefts| - 1]
    else
      null
  }

  function {:opaque} Right(): (r: Node?)
    reads Repr 
    requires Valid()
    ensures r != null ==>r in rights && r.Valid() 
  {
    if |rights| > 0 then
      rights[|rights| - 1]
    else
      null
  }

  function {:opaque} Value(): (v: int)
    reads this
    requires |values| > 0
    ensures v in values
  {
    values[|values| - 1]
  }

  ghost function{:opaque}  ValueSet(): (s: set<int>)
    reads Repr
    requires Valid()
    ensures s in ValueSets
  {
    ValueSets[|ValueSets| - 1]
  }

  function {:opaque} MaxMinVersionIndexHelper(version: int, versions: seq<int>, lo: int, hi: int): (index: int)
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
        MaxMinVersionIndexHelper(version, versions, mid + 1, hi)
      else 
        MaxMinVersionIndexHelper(version, versions, lo, mid - 1)
  } 

  function {:opaque} MaxMinVersionIndex(version: int, versions: seq<int>): (index: int)
    requires Sorted(versions)
    ensures -1 <= index < |versions|
    ensures index >= 0 <==> |versions| > 0 && versions[0] <= version
    ensures index == -1 || IsMaxMinVersion(version, versions[index], versions)
  {
    MaxMinVersionIndexHelper(version, versions, 0, |versions| - 1)
  }

  ghost function {:opaque} MaxMinVersionIndexForValueSets(version: int) : (index: int)
    reads this
    requires Sorted(ValueSetsVersions)
    requires |ValueSetsVersions| > 0
    ensures -1 <= index < |ValueSetsVersions|
    ensures index >= 0 <==> ValueSetsVersions[0] <= version
    ensures index == -1 || IsMaxMinVersion(version, ValueSetsVersions[index], ValueSetsVersions)
  {
    MaxMinVersionIndex(version, ValueSetsVersions)
  }

  ghost function {:opaque} ValueSetAtVersion(version: int) : (res: set<int>)
    reads Repr
    requires Valid()
    ensures Valid()
    ensures MaxMinVersionIndexForValueSets(version) >= 0 ==> 
              res == ValueSets[MaxMinVersionIndexForValueSets(version)]
  {
    var i := MaxMinVersionIndexForValueSets(version);
    if i == -1 then
      {}
    else
      ValueSets[i]
  }

  function {:opaque} MaxMinVersionIndexForValues(version: int) : (index: int)
    reads Repr
    requires Valid()
    ensures -1 <= index < |valuesVersions|
    ensures index >= 0 ==> IsMaxMinVersion(version, valuesVersions[index], valuesVersions)
    ensures index >= 0 ==> valuesVersions[index] in ValueSetsVersions
    ensures index <= MaxMinVersionIndexForValueSets(version)
  {
    var index := MaxMinVersionIndex(version, valuesVersions);
    if index >= 0 then
      assert exists i | 0 <= i < |ValueSetsVersions| :: 
              ValueSetsVersions[i] == valuesVersions[index] 
              && i >= index;
      index
    else
      index
  }

  function {:opaque} ValueAtVersion(version: int): (res: int)
    reads Repr 
    requires Valid() && ValueSetValid()
    ensures Valid()
    ensures MaxMinVersionIndexForValues(version) >= 0 ==> 
          res == values[MaxMinVersionIndexForValues(version)]
  {
    var i := MaxMinVersionIndexForValues(version);
    if i == -1 then
      -1
    else
      if |lefts| == 0 then
        if |rights| == 0 then
          assert values[i] in ValueSetAtVersion(version);
          values[i]
        else
          assert values[i] in ValueSetAtVersion(version);
          values[i]
      else
        assert values[i] in ValueSetAtVersion(version);
        values[i]
  }

  function MaxMinVersionIndexForRights(version: int) : (res: int)
    reads Repr
    requires Valid()
    ensures -1 <= res < |rights|
    ensures res == -1 && |rights| > 0 ==> rightsVersions[0] > version
    ensures res >= 0 ==> MaxMin(version, res, rightsVersions)
    ensures res >= 0 ==> rightsVersions[res] in ValueSetsVersions
    ensures res <= MaxMinVersionIndexForValueSets(version)
  {
    MaxMinVersion(version, rightsVersions)
  }

  // function RightAtVersion(version: int): (res: Node?)
  //   requires Valid()
  //   reads Repr 
  //   ensures res != null ==> res.Valid()
  //   ensures res != null ==> res.ValueSetAtVersion(version) <= ValueSetAtVersion(version)
  // {
  //   var i := MaxMinVersionIndexForRights(version);
  //   if i == -1 then
  //     null
  //   else
  //     rights[i]
  // }

  // function {:opaque} MaxMinVersionIndexForLefts(version: int) : (res: int)
  //   reads Repr
  //   requires Valid()
  //   ensures -1 <= res < |leftsVersions|
  //   ensures res == -1 && |leftsVersions| > 0 ==> leftsVersions[0] > version
  //   ensures res >= 0 ==> MaxMin(version, res, leftsVersions)
  //   ensures res >= 0 ==> leftsVersions[res] in ValueSetsVersions
  //   ensures res <= MaxMinVersionIndexForValueSets(version)
  // {
  //   MaxMinVersionIndex(version, leftsVersions)
  // }
  
  // function {:opaque} LeftAtVersion(version: int): (res: Node?)
  //   reads Repr
  //   requires Valid()
  //   ensures res != null ==> res in lefts && res.Valid()
  //   ensures res != null ==> res.ValueSetAtVersion(version) <= ValueSetAtVersion(version)
  // {
  //   var i := MaxMinVersionIndexForLefts(version);
  //   if i == -1 then
  //     null
  //   else
  //     lefts[i]
  // }

  // function Find(version: int, value: int): (found: bool)
  //   requires Valid()
  //   reads Repr
  //   decreases Repr
  //   // ensures found ==> value in ValueSetAtVersion(version).1
  //   // ensures value in ValueSetAtVersion(version).1 ==> found
  // {

  //   if MaxMinVersionIndexForValues(version) == -1 then 
  //     false
  //   else
  //     var x := ValueAtVersion(version);
  //     if x > value then
  //       var left := LeftAtVersion(version);
  //       if left == null then
  //         false
  //       else
  //         assert |lefts| > 0;
  //         var lf := left.Find(version, value);
  //         lf
  //     else if x < value then
  //       var right := RightAtVersion(version);
  //       if right == null then
  //         false
  //       else
  //         assert |rights| > 0;
  //         var rf := right.Find(version, value);
  //         rf
  //     else
  //       // assert value in ValueSetAtVersion(version);
  //       true
  // }

  // method Insert(time: int, value: int) returns (node: Node?)
  //   requires Valid()
  //   requires time > 0
  //   requires removed == -1
  //   requires time > ValueSets[|ValueSets| - 1].0
  //   modifies Repr
  //   decreases Repr
  //   ensures node == null ==> 
  //     Repr == old(Repr)
  //   ensures node != null ==> 
  //     fresh(node) &&
  //     node.Repr == {node} && 
  //     Repr == old(Repr) + {node} &&
  //     node.Valid()
  //   // ensures ValueSetAtVersion(time).0 != -1
  //   // ensures value in ValueSetAtVersion(time).1
  //   // ensures Valid()
  // {
  //   var x := Value();
  //   if x < value {
  //     var r := Right();
  //     if r == null {
  //       node := new Node.Init(time, value);
  //       assert node.Valid();
  //       rights := rights + [(time, node)];
  //       Repr := Repr + node.Repr;
  //       ValueSets := ValueSets + [(time, {x} + ValueSets[|ValueSets| - 1].1)];
  //     } else {
  //       node := r.Insert(time, value);
  //       if (node != null) {
  //         assert node.Valid();
  //         Repr := Repr + node.Repr;
  //         ValueSets := ValueSets + [(time, {x} + ValueSets[|ValueSets| - 1].1)];
  //       } 
  //     }
  //   } else if x > value {
  //     var l := Left();
  //     if l == null {
  //       node := new Node.Init(time, value);
  //       assert node.Valid();
  //       lefts := lefts + [(time, node)];
  //       Repr := Repr + node.Repr;
  //       ValueSets := ValueSets + [(time, {x} + ValueSets[|ValueSets| - 1].1)];
  //     } else {
  //       node := l.Insert(time, value);
  //       if (node != null) {
  //         assert node.Valid();
  //         // assert (forall r <- rights | r.1 != null :: r.1 !in l.Repr);  
  //         // assert (forall r <- rights | r.1 != null :: r.1 in Repr && r.1.Repr < Repr && this !in r.1.Repr && r.1.Valid());
  //         Repr := Repr + node.Repr;
  //         ValueSets := ValueSets + [(time, {x} + ValueSets[|ValueSets| - 1].1)];
  //       } 
  //     }
  //   } else {
  //     node := null;
  //   }
  // }

  // method DeleteMin(parent: Node, fromLeft: bool, time: int) returns (minV: int)
  //   requires Valid() && parent.Valid()
  //   requires parent.Left() == this || parent.Right() == this
  //   decreases Repr
  //   modifies parent.Repr
  //   ensures lefts == old(lefts)
  //   // ensures rights == old(rights)
  //   ensures parent.Valid()
  // {
  //   var l := Left();
  //   if l == null {
  //     assert Valid();
  //     if fromLeft {
  //       parent.lefts := parent.lefts + [(time, Right())];
  //     } else {
  //       parent.rights := parent.rights + [(time, Right())];
  //     }
  //     assert Valid();
  //     assert parent.Valid();
  //     minV := Value();
  //     assert parent.Valid();
  //     assert lefts == old(lefts);
  //   } else {
  //     assert Valid();
  //     minV := l.DeleteMin(this, true, time);
  //     assert lefts == old(lefts);
  //     assert Valid();
  //     // assert parent.Valid();
  //   }
  // }

  // method Delete(parent: Node?, fromLeft: bool, time: int, value: int) returns (root: Node?) 
  //   requires Valid()
  //   modifies Repr
  //   decreases Repr
  //   ensures root != null ==> root.Valid()
  // {
  //   var x := Value();
  //   var r := Right();
  //   var l := Left();
  //   if x == value {
  //     if r != null {
  //       var minV := r.DeleteMin(this, false, time);
  //       values := values + [(time, minV)];
  //     } else {
  //       if parent != null {
  //         if fromLeft {
  //           lefts := lefts + [(time, l)];
  //         } else {
  //           rights := rights + [(time, l)];
  //         }
  //       } else {
  //         root := l;
  //       }
  //     }
  //   } else if x < value {
  //     if r != null {
  //       root := r.Delete(this, false, time, value);
  //     }
  //   } else {
  //     if l != null {
  //       root := l.Delete(this, true, time, value);
  //     }
  //   }

  //   root := this;
  // }
}