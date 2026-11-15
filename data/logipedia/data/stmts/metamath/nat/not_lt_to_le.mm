$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_lt_to_le (logipedia__metamath__nat.not_lt_to_le), catalog title
  "nat.not_lt_to_le": for all natural numbers n and m, if n is not strictly
  less than m, then m is less than or equal to n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native strict and non-strict orders
  represent nat.lt and nat.le; the strict order is equivalent to the source
  definition nat.lt n m := nat.le (nat.S n) m. Native negation represents
  connectives.Not. The two restricted universal quantifiers, implication,
  negated strict inequality, and reversed non-strict conclusion preserve the
  source binder order, assumption, conclusion, and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-not-lt-to-le $a |-
  A. n e. NN0
    A. m e. NN0
      (
        -. n < m
        ->
        m <_ n
      )
$.
