$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.divides_to_congruent, catalog title "cong.divides_to_congruent":
  divisibility of the truncated difference of two ordered natural numbers by
  a positive modulus implies that they are congruent modulo that modulus.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The source definition
  congruent n m p means ( n mod p ) = ( m mod p ). The conditional
  if ( m <_ n , n - m , 0 ) is exactly the source truncated natural
  subtraction nat.minus n m. The declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d n m p $.

  logipedia-cong-divides-to-congruent $a |-
    A. n e. NN0 A. m e. NN0 A. p e. NN0
      (
        0 < p
        ->
        (
          m <_ n
          ->
          (
            p || if ( m <_ n , ( n - m ) , 0 )
            ->
            ( n mod p ) = ( m mod p )
          )
        )
      )
  $.
$}
