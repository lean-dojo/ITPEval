$(
  Statement-only formalization of Thousand Theorems corpus artifact Q257387
  (thousand-theorems__metamath__Q257387), "Vitali theorem": the range of any
  function selecting one representative from each
  rational-difference equivalence class of the real interval [0,1] is not
  Borel measurable.  This file contains no proof.
$)

$[ lib/set.mm $]

$c Q257387Relation Q257387Classes Q257387Selector $.

q257387-relation-syntax $a class Q257387Relation $.
q257387-classes-syntax $a class Q257387Classes $.
q257387-selector-syntax $a wff ( Q257387Selector F ) $.

${
  $d x y $.
  q257387-relation-definition $a
    |- Q257387Relation =
       { <. x , y >. |
         ( ( x e. ( 0 [,] 1 ) /\ y e. ( 0 [,] 1 ) )
           /\ ( x - y ) e. QQ ) } $.
$}

q257387-classes-definition $a
  |- Q257387Classes = ( ( 0 [,] 1 ) /. Q257387Relation ) $.

${
  $d F z $.
  q257387-selector-definition $a
    |- ( ( Q257387Selector F ) <->
         ( F Fn Q257387Classes /\
           A. z e. Q257387Classes ( F ` z ) e. z ) ) $.
$}

$(
  Q257387Selector spells out exactly the source lemma vRep_spec. The Lean
  proof uses no property of Classical.choose beyond this selector condition,
  so the target quantifies universally over selectors rather than weakening
  the statement to the existence of one non-Borel selector. BrSiga is the
  Borel sigma-algebra on RR, matching the source's default real MeasurableSet
  structure.
$)

thousand-theorems-metamath-Q257387 $a
  |- A. F
       ( ( Q257387Selector F ) ->
         -. ran F e. BrSiga ) $.
