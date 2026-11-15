$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_or_lt_eq (logipedia__metamath__nat.le_to_or_lt_eq), catalog title
  "nat.le_to_or_lt_eq": if one natural number is less than or equal to
  another, then it is either strictly less or equal. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native non-strict order, strict order, and
  equality on NN0 represent nat.le, nat.lt, and source natural-number
  equality. The restricted universal quantifiers, implication, and
  disjunction preserve the source binder order and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-le-to-or-lt-eq $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n <_ m
        ->
        ( n < m \/ n = m )
      )
$.
