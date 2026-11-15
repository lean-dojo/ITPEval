$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_n
  (logipedia__metamath__nat.le_n), catalog title "nat.le_n": every natural
  number is less than or equal to itself. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native non-strict order represents nat.le.
  The restricted universal quantifier preserves the source binder and its
  scope. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

logipedia-nat-le-n $a |-
  A. n e. NN0
    n <_ n
$.
