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
  ghost var ValueSets: seq<(int, set<int>)> 

  var created: int
  var removed: int
  var value: int
  var lefts: seq<(int, Node?)>
  var rights: seq<(int, Node?)>
  var data: seq<(int, int)>

  // Consistently use A && B ==> C when I wrote A ==> B ==> C
  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    created >= 0 
    && (removed == -1 || removed > created) 
    && |data| > 0 
    && data[0].0 == created 
    && ValueSets[0].0 == created
    && |ValueSets[0].1| == 1
    && this in Repr
    && (forall l <- lefts | l.1 != null ::
      l.1 in Repr && this !in l.1.Repr && l.1.Repr < Repr && l.1.Valid()
      && (forall timedValueSet <- l.1.ValueSets, timedData <- data, v | v in timedValueSet.1 :: v > timedData.1)) 
    && (forall r <- rights | r.1 != null ::
      r.1 in Repr && this !in r.1.Repr && r.1.Repr < Repr && r.1.Valid()
      && (forall timedValueSet <- r.1.ValueSets, timedData <- data, v | v in timedValueSet.1 :: v > timedData.1)) 
    && (forall r <- rights, l <- lefts | r.1 != null && l.1 != null :: 
      l.1 != r.1 && l.1.Repr !! r.1.Repr && l.0 != r.0) 
    // timestamps are strictly increasing in all sequences
    && (forall i, j | 0 <= i < j < |lefts| :: created < lefts[i].0 < lefts[j].0) 
    && (forall i, j | 0 <= i < j < |rights| :: created < rights[i].0 < rights[j].0) 
    && (forall i, j | 0 <= i < j < |data| :: created <= data[i].0 < data[j].0)
    && (forall i, j | 0 <= i < j < |ValueSets| :: created <= ValueSets[i].0 < ValueSets[j].0) 
    // all timestmps are larger than created
    && (forall i | 0 <= i < |ValueSets| :: ValueSets[i].0 >= created) 
    && (forall i | 0 <= i < |lefts| :: lefts[i].0 > created)
    && (forall i | 0 <= i < |rights| :: rights[i].0 > created)
    // timestamps much not violate the created and removed timestamps of each node
    && (forall i | 0 <= i < |lefts| && lefts[i].1 != null :: 
          lefts[i].1.created <= lefts[i].0 
          && (lefts[i].1.removed == -1 || lefts[i].0 <= lefts[i].1.removed))
    && (forall i | 0 <= i < |rights| && rights[i].1 != null :: 
          rights[i].1.created <= rights[i].0 
          && (rights[i].1.removed == -1 || rights[i].0 <= rights[i].1.removed))
    // all timestamps are smaller than removed
    && (removed > 0 ==>
        && (forall i | 0 <= i < |lefts| :: lefts[i].0 <= removed) 
        && (forall i | 0 <= i < |rights| :: rights[i].0 <= removed) 
        && (forall i | 0 <= i < |data| :: data[i].0 <= removed)
        && (forall i | 0 <= i < |ValueSets| :: ValueSets[i].0 <= removed)) 
    // data and ValueSets
    // && (forall node <- Repr, childTimedValueSet <- node.ValueSets | node != this :: 
    //       exists timedValueSet <- ValueSets ::
    //         childTimedValueSet.0 == timedValueSet.0 && childTimedValueSet.1 <= timedValueSet.1)
    && (forall node <- Repr, timedData <- node.data ::
          exists timedValueSet <- ValueSets :: 
            timedValueSet.0 == timedData.0 && timedData.1 in timedValueSet.1)
    && |ValueSets| >= |data|
    // ValueSets are updated exactly when data/ValueSets of lefts/ValueSets of rights get updated
    && (forall timedValueSet <- ValueSets ::
        (exists timedData <- data :: timedData.0 == timedValueSet.0 && timedData.1 in timedValueSet.1) ||
        (exists l <- lefts | l.1 != null ::
            exists lVS <- l.1.ValueSets :: lVS.0 == timedValueSet.0 && lVS.1 <= timedValueSet.1) ||
        (exists r <- rights | r.1 != null ::
            exists rVS <- r.1.ValueSets :: rVS.0 == timedValueSet.0 && rVS.1 <= timedValueSet.1))
  }

  predicate Sorted(s: seq<int>) 
  {
    (forall i, j | 0 <= i < j < |s| :: 0 <= s[i] < s[j])
    && (forall i | 0 <= i < |s| :: 0 <= s[i])
  }

  constructor Init(time: int, value: int)
    requires time > 0
    ensures Valid() && fresh(Repr)
    ensures created == time
    ensures removed == -1
    ensures lefts == []
    ensures rights == []
    ensures Repr == {this}
    ensures data == [(time, value)]
    ensures ValueSets == [(time, {value})]
  {
    created := time;
    removed := -1;
    lefts := [];
    rights := [];
    data := [(time, value)];
    Repr := {this};
    ValueSets := [(time, {value})];
  }

  function Left(): (l: Node?)
    reads Repr 
    requires Valid() 
    ensures Valid()
    ensures l != null ==> l.Valid()
  {
    if |lefts| > 0 then
      lefts[|lefts| - 1].1
    else
      null
  }

  function Right(): (r: Node?)
    reads Repr 
    requires Valid()
    ensures r != null ==> r.Valid()
  {
    if |rights| > 0 then
      rights[|rights| - 1].1
    else
      null
  }

  function Data(): int
    reads Repr
    requires Valid()
  {
    data[|data| - 1].1
  }

  ghost function ValueSet(): set<int>
    reads Repr
    requires Valid()
  {
    ValueSets[|ValueSets| - 1].1
  }

  ghost function ValueSetVersions(): (res: seq<int>)
    reads Repr
    requires Valid()
    ensures Valid()
    ensures Sorted(res)
    ensures |res| == |ValueSets|
    ensures forall i | 0 <= i < |ValueSets| :: res[i] == ValueSets[i].0
  { 
    assert Valid();
    // assert (forall i | 0 <= i < |data| :: 
    //       exists j | i <= j < |ValueSets| :: 
    //         ValueSets[j].0 == data[i].0 && data[i].1 in ValueSets[j].1);
    assert (forall timedData <- data :: 
           exists timedValueSet <- ValueSets :: 
             timedValueSet.0 == timedData.0 && timedData.1 in timedValueSet.1);
    seq(|ValueSets|, i requires 0 <= i < |ValueSets| 
                    requires Valid()
                    reads this, Repr => 
                    ValueSets[i].0)
  }

  function DataVersions(): (res: seq<int>)
    reads Repr
    requires Valid()
    ensures Sorted(res)
    ensures |res| == |data|
    ensures forall i | 0 <= i < |data| :: res[i] == data[i].0  
    ensures forall i | i in res :: i in ValueSetVersions()
  {
    seq(|data|, i requires 0 <= i < |data| 
                    requires Valid()
                    reads this, Repr => 
                    data[i].0)
  }

  function LeftVersions(): (res: seq<int>)
    reads Repr
    requires Valid()
    ensures Valid()
    ensures Sorted(res)
    ensures |res| == |lefts|
    ensures forall i | 0 <= i < |lefts| :: res[i] == lefts[i].0
  {
    seq(|lefts|, i requires 0 <= i < |lefts| 
                   reads this
                   => 
                   lefts[i].0)
  }

  function RightVersions(): (res: seq<int>)
    reads Repr
    requires Valid()
    ensures Valid()
    ensures Sorted(res)
    ensures |res| == |rights|
    ensures forall i | 0 <= i < |rights| :: res[i] == rights[i].0
  {
    seq(|rights|, i requires 0 <= i < |rights| 
                   reads this
                   => 
                   rights[i].0)
  }

  function IndexForVersion(version: int, s: seq<int>): (index: int)
    requires Sorted(s)
    requires version >= 0
    ensures -1 <= index < |s|
    ensures index == -1 <==> |s| == 0 || forall k :: 0 <= k < |s| ==> s[k] > version
    ensures index >= 0 ==> forall k :: index < k < |s| ==> s[k] > version
    ensures index >= 0 ==> |s| > 0
    ensures index >= 0 ==> forall k :: 0 <= k <= index ==> s[k] <= version
  {
    IndexForVersionHelper(version, s, 0, |s| - 1)
  }

  function IndexForVersionHelper(version: int, s: seq<int>, lo: int, hi: int): (index: int)
    decreases hi - lo
    requires |s| == 0 ==> lo > hi && hi == -1
    requires 0 <= lo <= |s| 
    requires -1 <= hi < |s|
    requires lo <= hi + 1
    requires Sorted(s)
    requires version >= 0
    requires forall k :: hi < k < |s| ==> s[k] > version
    requires forall k :: 0 <= k < lo ==> s[k] <= version
    ensures -1 <= index < |s|
    ensures index == -1 <==> (|s| == 0 || forall k :: 0 <= k < |s| ==> s[k] > version)
    ensures |s| > 0 && s[0] <= version ==> index >= 0
    ensures version in s ==> s[index] == version
    ensures index >= 0 ==> |s| > 0
    ensures forall k :: 0 <= k < index ==> s[k] < version && s[k] < s[index]
    ensures index == -1 || s[index] <= version
    ensures forall k :: index < k < |s| ==> s[k] > version
  {
    if (lo > hi) then
      assert lo <= 0 || s[lo - 1] <= version;
      lo - 1
    else
      assert |s| > 0;
      var mid := lo + (hi - lo) / 2;
      var v := s[mid];
      if v == version then
        mid
      else if v < version then
        IndexForVersionHelper(version, s, mid + 1, hi)
      else 
        IndexForVersionHelper(version, s, lo, mid - 1)
  } 

  ghost function ValueSetAtVersion(version: int) : (res: (int, set<int>))
    reads Repr
    requires version >= 0
    requires Valid()
    ensures res.0 >= 0 ==> res in ValueSets
    ensures res.0 <= version
    ensures res.0 >= 0 ==> res.0 in ValueSetVersions()
    ensures version in ValueSetVersions() <==> res.0 == version
  {
    var i := IndexForVersion(version, ValueSetVersions());
    if i == -1 then
      (-1, {})
    else
      assert forall k :: i < k < |ValueSets| ==> ValueSets[k].0 > version;
      assert forall k :: 0 <= k <= i ==> ValueSets[k].0 <= version;
      ValueSets[i]
  }

  function DataAtVersion(version: int): (res: (int, int))
    requires Valid()
    requires version >= 0
    reads Repr 
    ensures res.0 >= 0 ==> res in data
    ensures res.0 <= version
    ensures res.0 <= ValueSetAtVersion(version).0
    ensures res.0 >= 0 ==> res.0 in ValueSetVersions()
    ensures res.0 >= 0 ==> res.1 in ValueSetAtVersion(version).1
  {
    var i := IndexForVersion(version, DataVersions());
    if i == -1 then
      (-1, -1)
    else
      assert exists timedValueSet <- ValueSets :: 
            timedValueSet.0 == data[i].0;
      assert data[i].0 >= 0;
      data[i]
  }
  
  function LeftAtVersion(version: int): (res: (int, Node?))
    requires Valid()
    requires version >= 0
    reads Repr 
    ensures res.0 >= 0 && res.1 != null ==> res.1.created <= version && (res.1.removed == -1 || res.0 <= res.1.removed)
    ensures res.0 <= version
    ensures res.0 >= 0 ==> res in lefts
    ensures version in LeftVersions() ==> res.0 == version
  {
    var i := IndexForVersion(version, LeftVersions());
    if i == -1 then
      (-1, null)
    else
      lefts[i]
  }

  function RightAtVersion(version: int): (res: (int, Node?))
    requires Valid()
    requires version >= 0
    reads Repr 
    ensures res.0 >= 0 && res.1 != null ==> res.1.created <= version && (res.1.removed == -1 || version <= res.1.removed)
    ensures res.0 <= version
    ensures res.0 >= 0 ==> res in rights
    ensures version in RightVersions() ==> res.0 == version
  {
    var i := IndexForVersion(version, RightVersions());
    if i == -1 then
      (-1, null)
    else
      rights[i]
  }

  function Find(version: int, value: int): (found: bool)
    requires Valid()
    requires version >= 0
    reads Repr
    decreases Repr
    // ensures found ==> value in ValueSetAtVersion(version).1
    // ensures value in ValueSetAtVersion(version).1 ==> found
  {
    var (i, x) := DataAtVersion(version);
    assert i <= version;
    ghost var (_, r) := RightAtVersion(version);
    ghost var (_, l) := LeftAtVersion(version);
    // assert value in ValueSetAtVersion(version).1 <== 
    //     (x == value 
    //     || (r != null && value in r.ValueSetAtVersion(version).1) 
    //     || (l != null && value in l.ValueSetAtVersion(version).1));
    // assert i >= 0 ==> x in ValueSetAtVersion(version).1;
    // assert i == -1 <==> x !in ValueSetAtVersion(version).1;
    if i >= 0 then
      if x > value then
        var (li, left) := LeftAtVersion(version);
        // assert r != null ==> value !in r.ValueSetAtVersion(version).1;
        if left == null then
          // assert value !in ValueSetAtVersion(version).1;
          false
        else
          var lf := left.Find(version, value);
          // assert value in left.ValueSetAtVersion(version).1 ==> lf;
          lf
      else if x < value then
        var (ri, right) := RightAtVersion(version);
        // assert l != null ==> value !in l.ValueSetAtVersion(version).1;
        if right == null then
          // assert value !in ValueSetAtVersion(version).1;
          false
        else
          var rf := right.Find(version, value);
          // assert value in right.ValueSetAtVersion(version).1 ==> rf;
          rf
      else
        // assert value in ValueSetAtVersion(version).1;
        true
    else
      // assert value !in ValueSetAtVersion(version).1;
      false
  }

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
  //   var x := Data();
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
  //     minV := Data();
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
  //   var x := Data();
  //   var r := Right();
  //   var l := Left();
  //   if x == value {
  //     if r != null {
  //       var minV := r.DeleteMin(this, false, time);
  //       data := data + [(time, minV)];
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