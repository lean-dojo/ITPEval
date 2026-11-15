$(
  Statement-only formalization of the Logipedia corpus artifact nat.pred_Sn
  (logipedia__metamath__nat.pred_Sn), catalog title "nat.pred_Sn": every
  natural number is the predecessor of its successor. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and n + 1 represents the source
  successor nat.S n. The conditional exactly represents the source total
  predecessor nat.pred: it is zero at zero and subtracts one otherwise.
  Native equality represents source natural-number equality, and the
  restricted universal quantifier preserves the source binder and its scope.
  The final declaration is Metamath's native unproved $a statement encoding;
  this artifact adds no $p proof declaration.
$)

logipedia-nat-pred-sn $a |-
  A. n e. NN0
    n
    =
    if (
      ( n + 1 ) = 0 ,
      0 ,
      ( ( n + 1 ) - 1 )
    )
$.
