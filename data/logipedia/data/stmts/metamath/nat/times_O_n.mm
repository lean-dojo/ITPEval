$(
  Statement-only formalization of the Logipedia corpus artifact nat.times_O_n
  (logipedia__metamath__nat.times_O_n), catalog title "nat.times_O_n": zero is
  a left annihilator for multiplication on natural numbers, in the source
  orientation 0 = 0 times n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's zero, total multiplication, and native
  equality represent nat.O, nat.times, and logic.eq on that domain. The
  restricted universal quantifier preserves the source binder and its scope.
  The final declaration is Metamath's native unproved $a statement encoding;
  this artifact adds no $p proof declaration.
$)

logipedia-nat-times-o-n $a |-
  A. n e. NN0 ( 0 = ( 0 x. n ) )
$.
