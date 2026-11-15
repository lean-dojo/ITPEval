$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_to_eqb_true (logipedia__metamath__nat.eq_to_eqb_true), catalog title
  "nat.eq_to_eqb_true": equality of two natural numbers implies that their
  Boolean equality test returns true. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The Boolean carrier is {0,1}, with true represented
  by 1. For natural numbers n and m, if ( n = m , 1 , 0 ) is exactly the
  source equality test nat.eqb n m. Native SetMM equality represents
  logic.eq on both naturals and Booleans. Thus the restricted quantifiers,
  implication, and equality to 1 preserve the source statement without
  adding any hypothesis. The final declaration is Metamath's native unproved
  $a statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d m n $.

  logipedia-nat-eq-to-eqb-true $a |-
    A. n e. NN0
      A. m e. NN0
        (
          n = m
          ->
          if ( n = m , 1 , 0 ) = 1
        )
  $.
$}
