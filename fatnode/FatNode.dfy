// class Entry {
//   ghost var Repr: set<Node>

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

  var lefts: seq<(int, Node?)>
  var rights: seq<(int, Node?)>
  var values: seq<(int, int)>

  predicate Valid()
    reads this, Repr
  {
    |values| > 0 &&
    this in Repr &&
    (forall l :: l in lefts && l.1 != null ==> 
      l.1 in Repr && l.1.Repr < Repr && this !in l.1.Repr && l.1.Valid()) &&
    (forall r :: r in rights && r.1 != null ==> 
      r.1 in Repr && r.1.Repr < Repr && this !in r.1.Repr && r.1.Valid()) &&
    (forall r, l :: r in rights && l in lefts && r.1 != null && l.1 != null ==>
      l.1 != r.1 && l.1.Repr !! r.1.Repr) && // needed to add l.0 != r.0 
    // (forall i, j :: 0 <= i < j < |lefts| ==> lefts[i].0 < lefts[j].0) &&
    // (forall i, j :: 0 <= i < j < |rights| ==> rights[i].0 < rights[j].0) &&
    // (forall i, j :: 0 <= i < j < |values| ==> values[i].0 < values[j].0) 
    // COMMENT: The following does not hold due to the delete method
    (forall r1, r2 :: r1 in rights && r2 in rights && r1.1 != null && r2.1 != null  ==>
      r1 != r2 ==> r1.1.Repr !! r2.1.Repr) &&
    (forall l1, l2 :: l1 in lefts && l2 in lefts && l1.1 != null && l2.1 != null ==>
      l1 != l2 ==> l1.1.Repr !! l2.1.Repr)
  } 

  constructor Init(time: int, value: int)
    ensures Valid() && fresh(Repr)
    ensures lefts == []
    ensures rights == []
    ensures Repr == {this}
    ensures values == [(time, value)]
  {
    lefts := [];
    rights := [];
    values := [(time, value)];
    Repr := {this};
  }

  function method Left(): (l: Node?)
    reads Repr 
    requires Valid()
    ensures |values| > 0
    ensures l != null ==> l.Valid()
  {
    if |lefts| > 0 then
      lefts[|lefts| - 1].1
    else
      null
  }

  function method Right(): (r: Node?)
    reads Repr 
    requires Valid()
    ensures r != null ==> r.Valid()
  {
    if |rights| > 0 then
      rights[|rights| - 1].1
    else
      null
  }

  function method Value(): int
    reads Repr 
    requires Valid()
  {
    values[|values| - 1].1
  }

  function method ValueVersions(s: seq<(int, int)>): seq<int>
  {
    seq(|s|, i requires 0 <= i < |s| => s[i].0)
  }

  function method NodeVersions(s: seq<(int, Node?)>): seq<int>
  {
    seq(|s|, i requires 0 <= i < |s| => s[i].0)
  }

  function method BinarySearch(v: int, s: seq<int>, lo: int, hi: int): (index: int)
    requires |s| - 1 >= hi
    requires 0 <= lo <= hi + 1
    decreases hi - lo
    ensures -1 <= index < |s|
  {
    if |s| == 0 || v < s[0] || lo > hi then
      -1
    else
      var mid := lo + (hi - lo) / 2;
      var v' := s[mid];
      if v > v' then
        BinarySearch(v, s, mid + 1, hi)
      else if v < v' then
        BinarySearch(v, s, lo, mid - 1)
      else
        mid
  }

  function method FindValue(version: int): (bool, int)
    requires Valid()
    reads Repr 
  {
    var i := BinarySearch(version, ValueVersions(values), 0, |values| - 1);
    if i == -1 then
      (false, -1)
    else
      (true, values[i].1)
  }

  function method FindNode(version: int, left: bool): Node?
    requires Valid()
    reads Repr 
  {
    if left then
      var i := BinarySearch(version, NodeVersions(lefts), 0, |lefts| - 1);
      if i == -1 then
        null
      else
        lefts[i].1
    else
      var i := BinarySearch(version, NodeVersions(rights), 0, |rights| - 1);
      if i == -1 then
        null
      else
        rights[i].1
  }

  function method Find(version: int, value: int): bool
    requires Valid()
    reads Repr
  {
    var (found, x) := FindValue(version);
    if found then
      if x > Value() then
        var left := FindNode(version, true);
        if left == null then
          false
        else
          left.Find(version, value)
      else if x < Value() then
        var right := FindNode(version, false);
        if right == null then
          false
        else
          right.Find(version, value)
      else
        true
    else
      false
  }

  method Insert(time: int, value: int) returns (node: Node?)
    requires Valid()
    // requires time > maxTime
    modifies Repr
    decreases Repr
    ensures |values| > 0
    ensures node == null ==> 
      Repr == old(Repr)
    ensures node != null ==> 
      fresh(node) &&
      node.Repr == {node} && 
      // node.lefts == [] && node.rights == [] &&
      Repr == old(Repr) + {node} 
    ensures Valid()
  {
    var x := Value();
    if x < value {
      var r := Right();
      if r == null {
        node := new Node.Init(time, value);
        rights := rights + [(time, node)];
        Repr := Repr + node.Repr;
      } else {
        node := r.Insert(time, value);
        if (node != null) {
          Repr := Repr + node.Repr;
        } 
      }
    } else if x > value {
      var l := Left();
      if l == null {
        node := new Node.Init(time, value);
        lefts := lefts + [(time, node)];
        Repr := Repr + node.Repr;
      } else {
        node := l.Insert(time, value);
        if (node != null) {
          Repr := Repr + node.Repr;
        }
      }
    } else {
      node := null;
    }
  }

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