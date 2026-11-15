$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_plus_l
  (logipedia__metamath__nat.monotonic_le_plus_l), catalog title
  "nat.monotonic_le_plus_l": adding a fixed natural number on the right is
  monotone for the natural-number non-strict order. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native non-strict order
  represent nat.plus and nat.le. Expanding relations.monotonic gives the
  restricted quantifiers over m, x, and y and the implication below, preserving
  the source binder scopes, assumption, and conclusion. The final declaration
  is Metamath's native unproved $a statement encoding; this artifact adds no
  $p proof declaration.
$)

logipedia-nat-monotonic-le-plus-l $a |-
  A. m e. NN0
    A. x e. NN0
      A. y e. NN0
        (
          x <_ y
          ->
          ( x + m ) <_ ( y + m )
        )
$.
