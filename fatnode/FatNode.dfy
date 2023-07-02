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
    && this in Repr
    && (forall l <- lefts | l != null ::
        l in Repr && this !in l.Repr && l.Repr < Repr && l.Valid()) 
    && (forall r <- rights | r != null ::
        r in Repr && this !in r.Repr && r.Repr < Repr && r.Valid()) 
    && (forall r <- rights, l <- lefts | r != null && l != null :: 
        l != r && l.Repr !! r.Repr) 
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
    && ValueSetsValid()
  }

  ghost predicate ValueSetsValid()
    reads this
  {
    |values| == |valuesVersions|
    && |lefts| == |leftsVersions|
    && |rights| == |rightsVersions|
    && |ValueSetsVersions| == |ValueSets|
    && |ValueSets| >= |values| + |rights| + |lefts|
    && Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
    && |values| > 0 
    && (|lefts| == 0 && |rights| == 0 ==>
          |ValueSets| == |values| 
          && forall i | 0 <= i < |ValueSets| ::
              valuesVersions[i] == ValueSetsVersions[i] && ValueSets[i] == {values[i]})
    && (|lefts| > 0 && |rights| == 0 ==>
          forall i | 0 <= i < |ValueSets| ::
            exists j, k | 0 <= j <= i < |values| && 0 <= k <= i < |lefts| ::
              MaxMin(ValueSetsVersions[i], j, valuesVersions)
              && MaxMin(ValueSetsVersions[i], k, leftsVersions)
              && (leftsVersions[k] == ValueSetsVersions[i] || valuesVersions[j] == ValueSetsVersions[i])
              && (lefts[k] != null ==> 
                    exists x | 0 <= x < |lefts[k].ValueSets| 
                              && MaxMin(ValueSetsVersions[i], x, lefts[k].ValueSetsVersions) ::
                                ValueSets[i] == {values[j]} + lefts[k].ValueSets[x])
              && (lefts[k] == null ==> ValueSets[i] == {values[j]})) 
    && (|rights| > 0 && |lefts| == 0 ==>
          forall i | 0 <= i < |ValueSets| ::
            exists j, k | 0 <= j <= i < |values| && 0 <= k <= i < |rights| :: 
              MaxMin(ValueSetsVersions[i], j, valuesVersions)
              && MaxMin(ValueSetsVersions[i], k, rightsVersions)
              && (rightsVersions[k] == ValueSetsVersions[i] || valuesVersions[j] == ValueSetsVersions[i])
              && (rights[k] != null ==> 
                exists x | 0 <= x < |rights[k].ValueSets| 
                          && MaxMin(ValueSetsVersions[i], x, rights[k].ValueSetsVersions) ::
                            ValueSets[i] == {values[j]} + rights[k].ValueSets[x])
              && (rights[k] == null ==> ValueSets[i] == {values[j]})) 
    && (|rights| > 0 && |lefts| > 0 ==>
          forall i | 0 <= i < |ValueSets| ::
            exists j, k, l | 0 <= j <= i < |values| && 0 <= k <= i < |rights| && 0 <= l <= i < |lefts| ::
              MaxMin(ValueSetsVersions[i], j, valuesVersions)
              && MaxMin(ValueSetsVersions[i], k, rightsVersions)
              && MaxMin(ValueSetsVersions[i], l, leftsVersions)
              && (rightsVersions[k] == ValueSetsVersions[i]
                || leftsVersions[l] == ValueSetsVersions[i] 
                || valuesVersions[j] == ValueSetsVersions[i])
              && (lefts[l] != null && rights[k] != null ==> 
                    exists x, y | 0 <= x < |lefts[l].ValueSets| && 0 <= y < |rights[k].ValueSets| 
                                  && MaxMin(ValueSetsVersions[i], x, lefts[l].ValueSetsVersions)
                                  && MaxMin(ValueSetsVersions[i], y, rights[k].ValueSetsVersions) ::
                                    ValueSets[i] == {values[j]} + lefts[l].ValueSets[x] + rights[k].ValueSets[y])
              && (lefts[l] != null && rights[k] == null ==> 
                    exists x | 0 <= x < |lefts[l].ValueSets| 
                              && MaxMin(ValueSetsVersions[i], x, lefts[l].ValueSetsVersions) ::
                                ValueSets[i] == {values[j]} + lefts[l].ValueSets[x])
              && (rights[k] != null && lefts[l] == null ==> 
                    exists x | 0 <= x < |rights[k].ValueSets| 
                              && MaxMin(ValueSetsVersions[i], x, rights[k].ValueSetsVersions) ::
                                ValueSets[i] == {values[j]} + rights[k].ValueSets[x])
              && (rights[k] == null && lefts[l] == null ==> ValueSets[i] == {values[j]})) 
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

  predicate Sorted(s: seq<int>) 
  {
    (forall i, j | 0 <= i < j < |s| :: 0 <= s[i] < s[j])
    && (forall i | 0 <= i < |s| :: 0 <= s[i])
  }

  predicate MaxMin(version: int, index: int, versions: seq<int>)
    // requires Sorted(versions)
  {
    0 <= index < |versions| 
    && versions[index] <= version 
    && (forall i | 0 <= i < index :: versions[i] < version)
    && (forall i | index < i < |versions| :: versions[i] > version)
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

  function {:opaque} MaxMinVersionIndex(version: int, versions: seq<int>): (index: int)
    requires Sorted(versions)
    ensures -1 <= index < |versions|
    ensures index == -1 <==> |versions| == 0 || forall k :: 0 <= k < |versions| ==> versions[k] > version
    ensures |versions| > 0 && versions[0] <= version ==> index >= 0
    ensures index >= 0 ==> forall k :: index < k < |versions| ==> versions[k] > version
    ensures index >= 0 ==> |versions| > 0
    ensures index >= 0 ==> forall k :: 0 <= k <= index ==> versions[k] <= version
  {
    MaxMinVersionIndexHelper(version, versions, 0, |versions| - 1)
  }

  function MaxMinVersionIndexHelper(version: int, versions: seq<int>, lo: int, hi: int): (index: int)
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
    ensures |versions| > 0 && versions[0] <= version ==> index >= 0
    ensures version in versions ==> versions[index] == version
    ensures index >= 0 ==> |versions| > 0
    ensures index >= 0 ==> MaxMin(version, index, versions)
    ensures index == -1 || versions[index] <= version
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

  ghost function {:opaque} MaxMinVersionIndexForValueSets(version: int) : (res: int)
    reads this
    requires Sorted(ValueSetsVersions)
    requires |ValueSetsVersions| > 0
    ensures -1 <= res < |ValueSetsVersions|
    ensures res == -1 ==> ValueSetsVersions[0] > version
    ensures res >= 0 ==> MaxMin(version, res, ValueSetsVersions)
  {
    MaxMinVersionIndex(version, ValueSetsVersions)
  }

  ghost function {:opaque} ValueSetAtVersion(version: int) : (res: set<int>)
    reads this
    requires Sorted(ValueSetsVersions)
    requires |ValueSets| == |ValueSetsVersions|
    requires |ValueSets| > 0
    ensures MaxMinVersionIndexForValueSets(version) != -1 ==> res in ValueSets
  {
    var i := MaxMinVersionIndexForValueSets(version);
    if i == -1 then
      {}
    else
      ValueSets[i]
  }

  function MaxMinVersionIndexForValues(version: int) : (res: int)
    reads this
    requires ValueSetsValid()
    ensures -1 <= res < |valuesVersions|
    ensures res == -1 ==> valuesVersions[0] > version
    ensures res >= 0 ==> MaxMin(version, res, valuesVersions)
    ensures res >= 0 ==> valuesVersions[res] in ValueSetsVersions
    ensures res <= MaxMinVersionIndexForValueSets(version)
  {
    MaxMinVersionIndex(version, valuesVersions)
  }

  function ValueAtVersion(version: int): (res: int)
    requires Valid()
    reads Repr 
    ensures MaxMinVersionIndexForValues(version) >= 0 ==> res in values
    // ensures MaxMinVersionIndexForValues(version) >= 0 ==> res in ValueSetAtVersion(version)
  {
    var i := MaxMinVersionIndexForValues(version);
    if i == -1 then
      -1
    else
      assert valuesVersions[i] in ValueSetsVersions;
      // assert exists j | 0 <= j < |ValueSetsVersions| ::
      //   ValueSetsVersions[j] == valuesVersions[i] && values[i] in ValueSets[j];
      // assert (exists j | 0 <= j < |ValueSetsVersions| ::
      //   ValueSetsVersions[j] == valuesVersions[i] && values[i] in ValueSets[j]) ==> values[i] in ValueSetAtVersion(version);
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
    MaxMinVersionIndex(version, rightsVersions)
  }

  function RightAtVersion(version: int): (res: Node?)
    requires Valid()
    reads Repr 
    ensures res != null ==> res.Valid()
    // ensures res != null ==> res.ValueSetAtVersion(version) <= ValueSetAtVersion(version)
  {
    var i := MaxMinVersionIndexForRights(version);
    if i == -1 then
      null
    else
      rights[i]
  }

  function {:opaque} MaxMinVersionIndexForLefts(version: int) : (res: int)
    reads Repr
    requires Valid()
    ensures -1 <= res < |leftsVersions|
    ensures res == -1 && |leftsVersions| > 0 ==> leftsVersions[0] > version
    ensures res >= 0 ==> MaxMin(version, res, leftsVersions)
    ensures res >= 0 ==> leftsVersions[res] in ValueSetsVersions
    ensures res <= MaxMinVersionIndexForValueSets(version)
  {
    MaxMinVersionIndex(version, leftsVersions)
  }
  
  function {:opauqe} LeftAtVersion(version: int): (res: Node?)
    reads Repr
    requires Valid()
    // ensures res != null ==> res in lefts && res.ValueSetValid()
    // ensures res != null ==> res.ValueSetValid()
    // ensures res != null ==> res.ValueSetAtVersion(version) <= ValueSetAtVersion(version)
  {
    var i := MaxMinVersionIndexForLefts(version);
    if i == -1 then
      null
    else
      lefts[i]
  }

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