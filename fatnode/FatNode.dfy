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

datatype VersionedNode = VersionedNode(timeStamp: int, node: Node?)
datatype VersionedValue = VersionedValue(timeStamp: int, value: int)


class Node {
  ghost var Repr: set<Node>

  var lefts: seq<VersionedNode>
  var rights: seq<VersionedNode>
  var values: seq<VersionedValue>

  predicate Valid()
    reads this, Repr
  {
    |values| > 0 &&
    this in Repr &&
    (forall l <- lefts | l.node != null ::
      l.node in Repr && l.node.Repr < Repr && this !in l.node.Repr && l.node.Valid()) &&
    (forall r <- rights | r.node != null :: 
      r.node in Repr && r.node.Repr < Repr && this !in r.node.Repr && r.node.Valid()) &&
    (forall r <- rights, l <- lefts | r.node != null && l.node != null :: 
      l.node != r.node && l.node.Repr !! r.node.Repr) && // needed to add l.timeStamp != r.timeStamp 
    // (forall i, j :: 0 <= i < j < |lefts| ==> lefts[i].timeStamp < lefts[j].timeStamp) &&
    // (forall i, j :: 0 <= i < j < |rights| ==> rights[i].timeStamp < rights[j].timeStamp) &&
    // (forall i, j :: 0 <= i < j < |values| ==> values[i].timeStamp < values[j].timeStamp) 
    // COMMENT: The following does not hold due to the delete method
    // (forall r1 <- rights, r2 <- rights | r1.node != null && r2.node != null && r1 != r2 :: r1.node.Repr !! r2.node.Repr) &&
    (forall l1 <- lefts, l2 <- lefts | l1.node != null && l2.node != null && l1 != l2 :: l1.node.Repr !! l2.node.Repr)
  } 

  constructor Init(time: int, value: int)
    ensures Valid() && fresh(Repr)
    // ensures lefts == []
    // ensures rights == []
    ensures Repr == {this}
    // ensures values == [VersionedValue(time, value)]
  {
    lefts := [];
    rights := [];
    values := [VersionedValue(time, value)];
    Repr := {this};
  }

  function method Left(): (l: Node?)
    reads Repr 
    requires Valid()
    ensures |values| > 0
    ensures l != null ==> l.Valid()
  {
    if |lefts| > 0 then
      lefts[|lefts| - 1].node
    else
      null
  }

  function method Right(): (r: Node?)
    reads Repr 
    requires Valid()
    ensures r != null ==> r.Valid()
  {
    if |rights| > 0 then
      rights[|rights| - 1].node
    else
      null
  }

  function method Value(): int
    reads Repr 
    requires Valid()
  {
    values[|values| - 1].value
  }

  function method ValueVersions(s: seq<VersionedValue>): seq<int>
  {
    seq(|s|, i requires 0 <= i < |s| => s[i].timeStamp)
  }

  function method NodeVersions(s: seq<VersionedNode>): seq<int>
  {
    seq(|s|, i requires 0 <= i < |s| => s[i].timeStamp)
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
      (true, values[i].value)
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
        lefts[i].node
    else
      var i := BinarySearch(version, NodeVersions(rights), 0, |rights| - 1);
      if i == -1 then
        null
      else
        rights[i].node
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
        rights := rights + [VersionedNode(time, node)];
        Repr := Repr + node.Repr;
      } else {
        node := r.Insert(time, value);
        assert (forall r <- rights | r.node != null :: r.node in Repr && r.node.Repr < Repr && this !in r.node.Repr && r.node.Valid());
        if (node != null) {
          Repr := Repr + node.Repr;
        } 
      }
    } else if x > value {
      var l := Left();
      if l == null {
        node := new Node.Init(time, value);
        lefts := lefts + [VersionedNode(time, node)];
        Repr := Repr + node.Repr;
      } else {
        node := l.Insert(time, value);
        if (node != null) {
          // observe the following statement when changing from 
          //  (forall r <- rights, l <- lefts | r.node != null && l.node != null :: 
          //    l.node != r.node && l.node.Repr !! r.node.Repr)
          //  to
          // (forall r <- rights, l <- lefts | r.node != null && l.node != null && l.node != r.node :: 
          //    l.node.Repr !! r.node.Repr)
          assert (forall r <- rights | r.node != null :: r.node !in l.Repr);  
          assert (forall r <- rights | r.node != null :: r.node in Repr && r.node.Repr < Repr && this !in r.node.Repr && r.node.Valid());
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