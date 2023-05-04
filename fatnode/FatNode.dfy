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
    && |ValueSets| >= |values| + |rights| + |lefts|
    && Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
    && |values| > 0 
    && |ValueSets| > 0
    && this in Repr
    && (forall l <- lefts | l != null ::
        l in Repr && this !in l.Repr && l.Repr < Repr && l.Valid()) 
    && (forall r <- rights | r != null ::
        r in Repr && this !in r.Repr && r.Repr < Repr && r.Valid()) 
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
    // ValueSets are union of values of its own and its left and right children
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
  }

  lemma lemma1()
    requires Valid()
    ensures forall i | 0 <= i < |leftsVersions| :: leftsVersions[i] >= ValueSetsVersions[i]
    ensures forall i | 0 <= i < |rightsVersions| :: rightsVersions[i] >= ValueSetsVersions[i]
    ensures forall i | 0 <= i < |valuesVersions| :: valuesVersions[i] >= ValueSetsVersions[i]
  {}

  lemma lemma2()
    // COMMENT: lemma2 is the same as lemma1, except we unfold the Valid() predicate in lemma2
    requires |values| == |valuesVersions|
            && |lefts| == |leftsVersions|
            && |rights| == |rightsVersions|
            && |ValueSetsVersions| == |ValueSets|
            && |ValueSets| >= |values| + |rights| + |lefts|
            && Sorted(ValueSetsVersions) && Sorted(valuesVersions) && Sorted(leftsVersions) && Sorted(rightsVersions) 
            && |values| > 0 
            && |ValueSets| > 0
            && this in Repr
            && (forall l <- lefts | l != null ::
                l in Repr && this !in l.Repr && l.Repr < Repr && l.Valid()) 
            && (forall r <- rights | r != null ::
                r in Repr && this !in r.Repr && r.Repr < Repr && r.Valid()) 
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
            // ValueSets are union of values of its own and its left and right children
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
    ensures forall i | 0 <= i < |leftsVersions| :: leftsVersions[i] >= ValueSetsVersions[i]
    ensures forall i | 0 <= i < |rightsVersions| :: rightsVersions[i] >= ValueSetsVersions[i]
    ensures forall i | 0 <= i < |valuesVersions| :: valuesVersions[i] >= ValueSetsVersions[i]
  {}

  lemma lemma3()
    requires Sorted(leftsVersions) && Sorted (rightsVersions) && Sorted(valuesVersions) && Sorted(ValueSetsVersions) 
            && |ValueSetsVersions| >= |valuesVersions| + |rightsVersions| + |leftsVersions|
    requires (forall i | 0 <= i < |valuesVersions| ::
          exists j | i <= j < |ValueSetsVersions| ::
            valuesVersions[i] == ValueSetsVersions[j])
    && (forall i | 0 <= i < |leftsVersions| ::
          exists j | i <= j < |ValueSetsVersions| ::
            leftsVersions[i] == ValueSetsVersions[j])
    && (forall i | 0 <= i < |rightsVersions| ::
          exists j | i <= j < |ValueSetsVersions| ::
            rightsVersions[i] == ValueSetsVersions[j])
    ensures forall i | 0 <= i < |leftsVersions| :: leftsVersions[i] >= ValueSetsVersions[i]
    ensures forall i | 0 <= i < |rightsVersions| :: rightsVersions[i] >= ValueSetsVersions[i]
    ensures forall i | 0 <= i < |valuesVersions| :: valuesVersions[i] >= ValueSetsVersions[i]
  {}

  lemma lemma4()
    requires Valid()
    ensures forall i | 0 <= i < |rightsVersions| :: rightsVersions[i] >= ValueSetsVersions[i]
  {}

  // COMMENT: lemma5 and lemma4 seem to be able to be proven in a similar way, but lemma5 times out while lemma not
  lemma lemma5()
    requires Valid()
    ensures forall i | 0 <= i < |leftsVersions| :: leftsVersions[i] >= ValueSetsVersions[i]
  {}

  predicate Sorted(s: seq<int>) 
  {
    (forall i, j | 0 <= i < j < |s| :: 0 <= s[i] < s[j])
    && (forall i | 0 <= i < |s| :: 0 <= s[i])
  }

  predicate MaxMin(version: int, index: int, versions: seq<int>)
    // requires Sorted(versions)
  {
    0 <= index < |versions| 
    // && Sorted(versions) 
    && versions[index] <= version 
    && (forall i | 0 <= i < index :: versions[i] < version)
    && (forall i | index < i < |versions| :: versions[i] > version)
  }
}