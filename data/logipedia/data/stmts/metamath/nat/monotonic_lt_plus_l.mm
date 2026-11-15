$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_lt_plus_l
  (logipedia__metamath__nat.monotonic_lt_plus_l), catalog title
  "nat.monotonic_lt_plus_l": addition of a fixed natural number on the right
  is strictly monotone for the natural-number strict order. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native strict order
  represent nat.plus and nat.lt; on NN0, the latter is equivalent to the
  source definition nat.lt x y := nat.le (nat.S x) y. Expanding
  relations.monotonic gives the restricted quantifiers over n, x, and y and
  the implication below, preserving the source binder scopes, assumption, and
  conclusion. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-monotonic-lt-plus-l $a |-
  A. n e. NN0
    A. x e. NN0
      A. y e. NN0
        (
          x < y
          ->
          ( x + n ) < ( y + n )
        )
$.
