$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_not_lt (logipedia__metamath__nat.le_to_not_lt), catalog title
  "nat.le_to_not_lt": for all natural numbers n and m, if n is less than or
  equal to m, then m is not less than n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict and strict orders
  represent nat.le and nat.lt; the latter is equivalent to the source
  definition nat.lt n m := nat.le (nat.S n) m. The two restricted universal
  quantifiers, implication, and negated reversed strict inequality preserve
  the source binder order, hypothesis, conclusion, and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-le-to-not-lt $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n <_ m
        ->
        -. m < n
      )
$.
