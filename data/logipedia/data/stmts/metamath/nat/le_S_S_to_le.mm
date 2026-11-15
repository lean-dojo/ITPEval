$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_S_S_to_le (logipedia__metamath__nat.le_S_S_to_le), catalog title
  "nat.le_S_S_to_le": for all natural numbers n and m, if the successor of n
  is less than or equal to the successor of m, then n is less than or equal
  to m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict order represents
  nat.le, and adding one represents the source successor nat.S. The restricted
  universal quantifiers and implication preserve the source binder order,
  scopes, assumption, and conclusion. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-nat-le-S-S-to-le $a |-
  A. n e. NN0
    A. m e. NN0
      (
        ( n + 1 ) <_ ( m + 1 )
        ->
        n <_ m
      )
$.
