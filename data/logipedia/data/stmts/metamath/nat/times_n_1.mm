$(
  Statement-only formalization of the Logipedia corpus artifact nat.times_n_1
  (logipedia__metamath__nat.times_n_1), catalog title "nat.times_n_1": one is
  a right identity for multiplication on natural numbers, in the source
  orientation n = n times 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's one, total multiplication, and native equality
  represent nat.S nat.O, nat.times, and logic.eq on that domain. The restricted
  universal quantifier preserves the source binder and its scope. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-times-n-1 $a |-
  A. n e. NN0 ( n = ( n x. 1 ) )
$.
