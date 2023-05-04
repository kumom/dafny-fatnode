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
  predicate Valid()
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
      l.1 in Repr && this !in l.1.Repr && l.1.Repr < Repr && l.1.Valid()) 
    && (forall r <- rights | r.1 != null ::
      r.1 in Repr && this !in r.1.Repr && r.1.Repr < Repr &&r.1.Valid()) 
    && (forall r <- rights, l <- lefts | r.1 != null && l.1 != null :: 
      l.1 != r.1 && l.1.Repr !! r.1.Repr && l.0 != r.0) 
    && (forall i, j | 0 <= i < j < |lefts| :: created < lefts[i].0 < lefts[j].0) 
    && (forall i, j | 0 <= i < j < |rights| :: created < rights[i].0 < rights[j].0) 
    && (forall i, j | 0 <= i < j < |data| :: created <= data[i].0 < data[j].0)
    && (forall i, j | 0 <= i < j < |ValueSets| :: created <= ValueSets[i].0 < ValueSets[j].0) 
    && (forall i | 0 <= i < |ValueSets| :: ValueSets[i].0 >= created) 
    && (forall i | 0 <= i < |data| :: data[i].0 >= created)
    && (forall i | 0 <= i < |lefts| :: lefts[i].0 > created)
    && (forall i | 0 <= i < |rights| :: rights[i].0 > created)
    && (removed > 0 ==>
        && (forall i | 0 <= i < |lefts| :: lefts[i].0 < removed) 
        && (forall i | 0 <= i < |rights| :: rights[i].0 < removed) 
        && (forall i | 0 <= i < |data| :: data[i].0 < removed)) 
    // data and ValueSets
    && (forall timedValueSet <- ValueSets ::  
        created <= timedValueSet.0 && (removed == -1 || timedValueSet.0 <= removed)) 
    && (forall timedValueSet <- ValueSets, node <- Repr, childTimedValueSet <- node.ValueSets :: 
        childTimedValueSet.0 <= timedValueSet.0 ==> childTimedValueSet.1 <= timedValueSet.1) 
    && (forall i | 0 <= i < |data| :: 
          exists j | i <= j < |ValueSets| :: 
            ValueSets[j].0 == data[i].0 && data[i].1 in ValueSets[j].1)
  }

  function ValueSetVersions(): (res: seq<int>)
    reads Repr
    requires Valid()
    ensures Valid()
    // COMMENT: This assertion is literally part of Valid()
    ensures forall i | 0 <= i < |data| :: 
             exists j | i <= j < |ValueSets| :: 
              ValueSets[j].0 == data[i].0 && data[i].1 in ValueSets[j].1
  { 
    seq(|ValueSets|, i requires 0 <= i < |ValueSets| 
                    requires Valid()
                    reads this, Repr => 
                    ValueSets[i].0)
  }
}