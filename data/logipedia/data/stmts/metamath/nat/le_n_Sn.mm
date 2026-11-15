$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_n_Sn
  (logipedia__metamath__nat.le_n_Sn), catalog title "nat.le_n_Sn": every
  natural number is less than or equal to its successor. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native non-strict order represents nat.le,
  and n + 1 represents the source successor nat.S n. The restricted universal
  quantifier preserves the source binder and its scope. The final declaration
  is Metamath's native unproved $a statement encoding; this artifact introduces
  no $p proof declaration.
$)

logipedia-nat-le-n-Sn $a |-
  A. n e. NN0
    n <_ ( n + 1 )
$.
