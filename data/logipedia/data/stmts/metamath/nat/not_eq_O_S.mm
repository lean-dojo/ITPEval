$(
  Statement-only formalization of the Logipedia corpus artifact nat.not_eq_O_S
  (logipedia__metamath__nat.not_eq_O_S), catalog title "nat.not_eq_O_S":
  zero is not equal to the successor of any natural number. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, n + 1 represents nat.S n,
  native equality represents logic.eq on natural numbers, and native negation
  represents connectives.Not. The restricted universal quantifier preserves
  the source binder and scope. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-nat-not-eq-o-s $a |-
  A. n e. NN0
    -. 0 = ( n + 1 )
$.
