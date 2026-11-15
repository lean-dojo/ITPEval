$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.eq_times_plus_to_congruent, catalog title
  "cong.eq_times_plus_to_congruent": if a natural number equals a natural
  multiple of a positive modulus plus another natural number, then the two
  numbers are congruent modulo that modulus. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The source definition
  congruent n m p means ( n mod p ) = ( m mod p ), so the conclusion below
  is its exact definition-expanded form. The declaration is an unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d n m p r $.

  logipedia-cong-eq-times-plus-to-congruent $a |-
    A. n e. NN0 A. m e. NN0 A. p e. NN0 A. r e. NN0
      (
        0 < p
        ->
        (
          n = ( ( r x. p ) + m )
          ->
          ( n mod p ) = ( m mod p )
        )
      )
  $.
$}
