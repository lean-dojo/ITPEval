$(
  Statement-only formalization of the Logipedia corpus artifact nat.not_eq_S
  (logipedia__metamath__nat.not_eq_S), catalog title "nat.not_eq_S": for all
  natural numbers n and m, if n is not equal to m, then the successor of n is
  not equal to the successor of m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Adding one represents the source successor nat.S,
  native equality represents logic.eq on natural numbers, and native negation
  represents connectives.Not. The two restricted universal quantifiers and
  implication preserve the source binder order, hypothesis, conclusion, and
  all scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

logipedia-nat-not-eq-s $a |-
  A. n e. NN0
    A. m e. NN0
      (
        -. n = m
        ->
        -. ( n + 1 ) = ( m + 1 )
      )
$.
