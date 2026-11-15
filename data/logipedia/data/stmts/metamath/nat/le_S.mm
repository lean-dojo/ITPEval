$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_S
  (logipedia__metamath__nat.le_S), catalog title "nat.le_S": for all natural
  numbers n and m, n less than or equal to m implies n less than or equal to
  the successor of m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict order represents
  nat.le, and m + 1 represents the source successor nat.S m. The restricted
  universal quantifiers and implication preserve the source binder order,
  scopes, assumption, and conclusion. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-nat-le-S $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n <_ m
        ->
        n <_ ( m + 1 )
      )
$.
