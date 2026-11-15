$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_to_leb_false
  (logipedia__metamath__nat.not_le_to_leb_false), catalog title
  "nat.not_le_to_leb_false": if one natural number is not less than or equal
  to another, their Boolean less-than-or-equal test returns false. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native non-strict order on NN0 represents
  nat.le, and native negation represents connectives.Not. The Boolean carrier
  is {0,1}, with false represented by 0, and if ( n <_ m , 1 , 0 ) is the
  characteristic Boolean function of that order, definitionally representing
  the source nat.leb n m. Native SetMM equality represents logic.eq on
  Booleans. Thus the restricted universal quantifiers, negated order
  assumption, implication, and equality to 0 preserve the source statement
  without adding any hypothesis. The final declaration is Metamath's native
  unproved $a statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d m n $.

  logipedia-nat-not-le-to-leb-false $a |-
    A. n e. NN0
      A. m e. NN0
        (
          -. n <_ m
          ->
          if ( n <_ m , 1 , 0 ) = 0
        )
  $.
$}
