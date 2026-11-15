$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_pred_n
  (logipedia__metamath__nat.le_pred_n), catalog title "nat.le_pred_n": every
  natural number's predecessor is less than or equal to that number. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The conditional is exactly the source total
  predecessor nat.pred: it is zero at zero and n - 1 otherwise. SetMM's native
  non-strict order represents nat.le. The restricted universal quantifier
  preserves the source binder and its scope. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

logipedia-nat-le-pred-n $a |-
  A. n e. NN0
    if (
      n = 0 ,
      0 ,
      ( n - 1 )
    )
    <_
    n
$.
