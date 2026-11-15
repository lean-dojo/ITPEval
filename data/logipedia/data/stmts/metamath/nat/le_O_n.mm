$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_O_n
  (logipedia__metamath__nat.le_O_n), catalog title "nat.le_O_n": zero is
  less than or equal to every natural number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, and its native
  non-strict order on NN0 represents nat.le. The restricted universal
  quantifier exactly preserves the source forall binder and its scope. The
  final declaration is Metamath's native unproved $a statement encoding;
  this artifact adds no $p proof declaration.
$)

logipedia-nat-le-O-n $a |-
  A. n e. NN0 ( 0 <_ n )
$.
