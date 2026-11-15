$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.congruent_times, catalog title "cong.congruent_times": multiplication
  preserves congruence of natural numbers modulo a positive natural modulus.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The source definition
  congruent a b p means ( a mod p ) = ( b mod p ). Variables r and s
  represent the source variables n1 and m1, respectively. The declaration
  is an unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d n m r s p $.

  logipedia-cong-congruent-times $a |-
    A. n e. NN0 A. m e. NN0 A. r e. NN0 A. s e. NN0 A. p e. NN0
      (
        0 < p
        ->
        (
          ( n mod p ) = ( r mod p )
          ->
          (
            ( m mod p ) = ( s mod p )
            ->
            ( ( n x. m ) mod p ) = ( ( r x. s ) mod p )
          )
        )
      )
  $.
$}
