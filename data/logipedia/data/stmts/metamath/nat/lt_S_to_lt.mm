$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_S_to_lt (logipedia__metamath__nat.lt_S_to_lt), catalog title
  "nat.lt_S_to_lt": for all natural numbers n and m, if the successor of n
  is strictly less than m, then n is strictly less than m. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native strict order represents nat.lt,
  equivalently nat.lt n m := nat.le (nat.S n) m, and n + 1 represents the
  source successor nat.S n. The restricted universal quantifiers and
  implication preserve the source binder order, scopes, assumption, and
  conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

logipedia-nat-lt-S-to-lt $a |-
  A. n e. NN0
    A. m e. NN0
      (
        ( n + 1 ) < m
        ->
        n < m
      )
$.
