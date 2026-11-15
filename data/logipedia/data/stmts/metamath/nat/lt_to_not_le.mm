$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_not_le (logipedia__metamath__nat.lt_to_not_le), catalog title
  "nat.lt_to_not_le": for all natural numbers n and m, if n is strictly less
  than m, then m is not less than or equal to n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native strict and non-strict orders
  represent nat.lt and nat.le; the strict order is equivalent to the source
  definition nat.lt n m := nat.le (nat.S n) m. Native negation represents
  connectives.Not. The two restricted universal quantifiers, implication, and
  negated reversed non-strict inequality preserve the source binder order,
  hypothesis, conclusion, and all scopes. The artifact's final declaration is
  Metamath's native unproved $a statement encoding; this artifact supplies no
  $p proof declaration.
$)

logipedia-nat-lt-to-not-le $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n < m
        ->
        -. m <_ n
      )
$.
