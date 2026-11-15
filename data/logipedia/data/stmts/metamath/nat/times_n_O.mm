$(
  Statement-only formalization of the Logipedia corpus artifact nat.times_n_O
  (logipedia__metamath__nat.times_n_O), catalog title "nat.times_n_O": zero is
  a right annihilator for multiplication on natural numbers, in the source
  orientation 0 = n times 0. This file contains no proof.
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

logipedia-nat-times-n-o $a |-
  A. n e. NN0 ( 0 = ( n x. 0 ) )
$.
