$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eqb_true_to_eq (logipedia__metamath__nat.eqb_true_to_eq), catalog title
  "nat.eqb_true_to_eq": if the Boolean equality test on two natural numbers
  returns true, then the natural numbers are equal. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The Boolean carrier is {0,1}, with true represented
  by 1. For natural numbers n and m, if ( n = m , 1 , 0 ) is exactly the
  source Boolean equality test nat.eqb n m. Native SetMM equality represents
  logic.eq on both naturals and Booleans. Thus the restricted quantifiers,
  implication, equality to 1, and concluding natural-number equality preserve
  the source statement without adding any hypothesis. The final declaration
  is Metamath's native unproved $a statement encoding; this artifact adds no
  $p proof declaration.
$)

${
  $d m n $.

  logipedia-nat-eqb-true-to-eq $a |-
    A. n e. NN0
      A. m e. NN0
        (
          if ( n = m , 1 , 0 ) = 1
          ->
          n = m
        )
  $.
$}
