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
    && |ValueSets| >= |data|
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
    && (forall i, j | 0 <= i < j < |lefts| :: created < lefts[i].0 < lefts[j].0) 
    && (forall i, j | 0 <= i < j < |rights| :: created < rights[i].0 < rights[j].0) 
    && (forall i, j | 0 <= i < j < |data| :: created <= data[i].0 < data[j].0)
    && (forall i, j | 0 <= i < j < |ValueSets| :: created <= ValueSets[i].0 < ValueSets[j].0) 
    && (forall i | 0 <= i < |ValueSets| :: ValueSets[i].0 >= created) 
    && (forall i | 0 <= i < |data| :: data[i].0 >= created && data[i].0 <= ValueSets[i].0)
    && (forall i | 0 <= i < |lefts| :: lefts[i].0 > created 
                  && (lefts[i].1 != null ==> (lefts[i].1.created <= lefts[i].0 
                                          && lefts[i].1.removed == -1 && lefts[i].0 <= lefts[i].1.removed)))
    && (forall i | 0 <= i < |rights| :: rights[i].0 > created 
                  && (rights[i].1 != null ==> (rights[i].1.created <= rights[i].0
                                          && rights[i].1.removed == -1 && rights[i].0 <= rights[i].1.removed)))
    && (removed > 0 ==>
        && (forall i | 0 <= i < |lefts| :: lefts[i].0 <= removed) 
        && (forall i | 0 <= i < |rights| :: rights[i].0 <= removed) 
        && (forall i | 0 <= i < |data| :: data[i].0 <= removed)
        && (forall i | 0 <= i < |ValueSets| :: ValueSets[i].0 <= removed)) 
    // data and ValueSets
    // && (forall timedValueSet <- ValueSets, node <- Repr, childTimedValueSet <- node.ValueSets :: 
    //     childTimedValueSet.0 == timedValueSet.0 ==> childTimedValueSet.1 <= timedValueSet.1) 
    && (forall node <- Repr, childTimedValueSet <- node.ValueSets | node != this :: 
          exists timedValueSet <- ValueSets ::
            childTimedValueSet.0 == timedValueSet.0 && childTimedValueSet.1 <= timedValueSet.1)
    && (forall node <- Repr, timedData <- node.data ::
          exists timedValueSet <- ValueSets :: 
            timedValueSet.0 == timedData.0 && timedData.1 in timedValueSet.1)
    && (forall timedValueSet <- ValueSets ::
        (exists timedData <- data :: timedData.0 == timedValueSet.0) ||
        (exists l <- lefts | l.1 != null ::
            exists lVS <- l.1.ValueSets :: lVS.0 == timedValueSet.0) ||
        (exists r <- rights | r.1 != null ::
            exists rVS <- r.1.ValueSets :: rVS.0 == timedValueSet.0))
  }

  predicate Sorted(s: seq<int>) 
  {
    (forall i, j | 0 <= i < j < |s| :: 0 <= s[i] < s[j])
    && (forall i | 0 <= i < |s| :: 0 <= s[i])
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
    ensures index == -1 <==> |s| == 0 || forall k :: 0 <= k < |s| ==> s[k] > version
    ensures |s| > 0 && s[0] <= version ==> index >= 0
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
    ensures version in DataVersions() ==> res.0 == version
    ensures res.0 == ValueSetAtVersion(version).0
    ensures res.0 >= 0 ==> res.1 in ValueSetAtVersion(version).1
  {
    var i := IndexForVersion(version, DataVersions());
    if i == -1 then
      (-1, -1)
    else
      assert data[i].0 >= 0;
      // COMMENT: This line drastically changes verification time
      assert data[i].1 in ValueSetAtVersion(version).1;
      data[i]
  }
  
}