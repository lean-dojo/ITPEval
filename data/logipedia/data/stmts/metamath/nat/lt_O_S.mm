$(
  Statement-only formalization of the Logipedia corpus artifact nat.lt_O_S
  (logipedia__metamath__nat.lt_O_S), catalog title "nat.lt_O_S": zero is
  strictly less than the successor of every natural number. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, n + 1 represents the
  source successor nat.S n, and its native strict order on NN0 represents
  nat.lt. The restricted universal quantifier exactly preserves the source
  forall binder and its scope. The final declaration is Metamath's native
  unproved $a statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-lt-O-S $a |-
  A. n e. NN0
    0 < ( n + 1 )
$.
