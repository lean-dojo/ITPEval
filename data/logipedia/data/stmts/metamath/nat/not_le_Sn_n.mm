$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_Sn_n (logipedia__metamath__nat.not_le_Sn_n), catalog title
  "nat.not_le_Sn_n": the successor of every natural number is not less than
  or equal to that number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's n + 1 represents nat.S n, its native
  non-strict order on NN0 represents nat.le, and native negation represents
  connectives.Not. The restricted universal quantifier preserves the source
  binder and scope. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

logipedia-nat-not-le-sn-n $a |-
  A. n e. NN0
    -. ( n + 1 ) <_ n
$.
