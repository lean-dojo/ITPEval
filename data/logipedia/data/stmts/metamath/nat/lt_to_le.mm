$(
  Statement-only formalization of the Logipedia corpus artifact nat.lt_to_le
  (logipedia__metamath__nat.lt_to_le), catalog title "nat.lt_to_le": for all
  natural numbers x and y, if x is strictly less than y, then x is less than
  or equal to y. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native strict and non-strict orders
  represent nat.lt and nat.le. The strict order is equivalent to the source
  definition nat.lt x y := nat.le (nat.S x) y because, on natural numbers,
  x < y exactly when x + 1 <_ y. The restricted universal quantifiers and
  implication preserve both source binders, their scopes, the assumption, and
  the conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

logipedia-nat-lt-to-le $a |-
  A. x e. NN0
    A. y e. NN0
      (
        x < y
        ->
        x <_ y
      )
$.
