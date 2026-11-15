$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1457052
  (thousand-theorems__metamath__Q1457052), "Well-ordering theorem": every
  arbitrary set can be equipped with a well-order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's predicate r We x states that r is both a strict linear order and a
  well-founded relation on the set x. Thus the existentially quantified
  relation r is equivalent to Lean's existential LinearOrder structure
  together with WellFoundedLT on an arbitrary type represented by the set
  carrier x. The final declaration is the single unproved corpus $a statement;
  the root artifact contains no $p declaration; the included lib/set.mm
  supplies the proved standard library.
$)

${
  $d x r $.

  thousand-theorems-q1457052-well-ordering $a |-
    A. x E. r r We x
  $.
$}
