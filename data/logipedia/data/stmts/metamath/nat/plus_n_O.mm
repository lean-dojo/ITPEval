$(
  Statement-only formalization of the Logipedia corpus artifact nat.plus_n_O
  (logipedia__metamath__nat.plus_n_O), catalog title "nat.plus_n_O": zero is
  a right identity for addition on natural numbers, in the source orientation
  n = n + 0. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's zero, total addition, and native equality
  represent nat.O, nat.plus, and logic.eq on that domain. The restricted
  universal quantifier preserves the source binder and its scope. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-plus-n-o $a |-
  A. n e. NN0 ( n = ( n + 0 ) )
$.
