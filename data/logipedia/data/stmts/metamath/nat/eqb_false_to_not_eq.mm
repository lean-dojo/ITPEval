$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eqb_false_to_not_eq
  (logipedia__metamath__nat.eqb_false_to_not_eq), catalog title
  "nat.eqb_false_to_not_eq": if the Boolean equality test on two natural
  numbers returns false, then the natural numbers are not equal. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The Boolean carrier is {0,1}, with false represented
  by 0. For natural numbers n and m, if ( n = m , 1 , 0 ) is exactly the
  source Boolean equality test nat.eqb n m. Native SetMM equality represents
  logic.eq on both naturals and Booleans, and native negation represents
  connectives.Not. Thus the restricted quantifiers, implication, equality to
  0, and negated equality preserve the source statement without adding any
  hypothesis. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d m n $.

  logipedia-nat-eqb-false-to-not-eq $a |-
    A. n e. NN0
      A. m e. NN0
        (
          if ( n = m , 1 , 0 ) = 0
          ->
          -. n = m
        )
  $.
$}
