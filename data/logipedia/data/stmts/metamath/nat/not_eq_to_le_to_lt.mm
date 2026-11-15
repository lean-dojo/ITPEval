$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_eq_to_le_to_lt
  (logipedia__metamath__nat.not_eq_to_le_to_lt), catalog title
  "nat.not_eq_to_le_to_lt": for all natural numbers n and m, if n is not
  equal to m and n is less than or equal to m, then n is strictly less than
  m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Native SetMM equality and negation represent
  logic.eq on naturals and connectives.Not. On NN0, SetMM's native non-strict
  and strict orders represent nat.le and nat.lt; the latter is equivalent to
  the source definition nat.lt n m := nat.le (nat.S n) m. The restricted
  universal quantifiers and nested implications preserve the source binder
  order, hypotheses, conclusion, and all scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-nat-not-eq-to-le-to-lt $a |-
  A. n e. NN0
    A. m e. NN0
      (
        -. n = m
        ->
        (
          n <_ m
          ->
          n < m
        )
      )
$.
