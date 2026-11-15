$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_plus_n
  (logipedia__metamath__nat.le_plus_n), catalog title "nat.le_plus_n": every
  natural number m is less than or equal to n + m for every natural number n.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native non-strict order
  represent nat.plus and nat.le. The two restricted universal quantifiers
  preserve the source binder order and scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-nat-le-plus-n $a |-
  A. n e. NN0
    A. m e. NN0
      m <_ ( n + m )
$.
