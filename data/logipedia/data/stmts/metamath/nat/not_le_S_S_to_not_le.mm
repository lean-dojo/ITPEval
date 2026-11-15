$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_S_S_to_not_le
  (logipedia__metamath__nat.not_le_S_S_to_not_le), catalog title
  "nat.not_le_S_S_to_not_le": for all natural numbers n and m, if the
  successor of n is not less than or equal to the successor of m, then n is
  not less than or equal to m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict order represents
  nat.le, adding one represents the source successor nat.S, and native
  negation represents connectives.Not. The restricted universal quantifiers
  and implication preserve the source binder order, scopes, assumption, and
  conclusion. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

logipedia-nat-not-le-s-s-to-not-le $a |-
  A. n e. NN0
    A. m e. NN0
      (
        -. ( n + 1 ) <_ ( m + 1 )
        ->
        -. n <_ m
      )
$.
