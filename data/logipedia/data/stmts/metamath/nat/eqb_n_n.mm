$(
  Statement-only formalization of the Logipedia corpus artifact nat.eqb_n_n
  (logipedia__metamath__nat.eqb_n_n), catalog title "nat.eqb_n_n": the
  Boolean equality test of every natural number with itself returns true.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The Boolean carrier is {0,1}, with true represented
  by 1 and false by 0. For a natural number n, if ( n = n , 1 , 0 ) is
  exactly the source Boolean equality test nat.eqb n n. Native SetMM equality
  represents logic.eq on Booleans. Thus the restricted universal quantifier
  and equality to 1 preserve the source statement without adding any
  hypothesis. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-eqb-n-n $a |-
  A. n e. NN0
    if ( n = n , 1 , 0 ) = 1
$.
