$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.congruent_n_n, catalog title "cong.congruent_n_n": every natural
  number is congruent to itself modulo every natural modulus. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The source definition
  congruent n m p means ( n mod p ) = ( m mod p ), so the conclusion below
  is its exact definition-expanded form with m = n. The declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d n p $.

  logipedia-cong-congruent-n-n $a |-
    A. n e. NN0 A. p e. NN0
      ( n mod p ) = ( n mod p )
  $.
$}
