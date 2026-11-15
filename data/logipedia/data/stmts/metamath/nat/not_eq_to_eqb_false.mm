$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_eq_to_eqb_false
  (logipedia__metamath__nat.not_eq_to_eqb_false), catalog title
  "nat.not_eq_to_eqb_false": inequality of two natural numbers implies that
  their Boolean equality test returns false. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The Boolean carrier is {0,1}, with false represented
  by 0. For natural numbers n and m, if ( n = m , 1 , 0 ) is exactly the
  source Boolean equality test nat.eqb n m. Native SetMM inequality represents
  connectives.Not applied to logic.eq on naturals, and native equality
  represents logic.eq on Booleans. Thus the restricted quantifiers,
  implication, inequality, and equality to 0 preserve the source statement
  without adding any hypothesis. The final declaration is Metamath's native
  unproved $a statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d m n $.

  logipedia-nat-not-eq-to-eqb-false $a |-
    A. n e. NN0
      A. m e. NN0
        (
          n =/= m
          ->
          if ( n = m , 1 , 0 ) = 0
        )
  $.
$}
