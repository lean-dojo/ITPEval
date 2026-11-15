$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.congruent_n_mod_n, catalog title "cong.congruent_n_mod_n": every
  natural number is congruent modulo a positive natural modulus to its
  remainder modulo that modulus. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The source definition
  congruent n m p means ( n mod p ) = ( m mod p ), so the conclusion below
  is its exact definition-expanded form with m = ( n mod p ). The declaration
  is an unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d n p $.

  logipedia-cong-congruent-n-mod-n $a |-
    A. n e. NN0 A. p e. NN0
      (
        0 < p
        ->
        ( n mod p ) = ( ( n mod p ) mod p )
      )
  $.
$}
