$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.congruent_to_divides, catalog title "cong.congruent_to_divides":
  congruent natural numbers modulo a positive natural modulus have a
  truncated difference divisible by that modulus. This file contains no
  proof.
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

  logipedia-cong-congruent-to-divides $a |-
    A. n e. NN0 A. m e. NN0 A. p e. NN0
      (
        0 < p
        ->
        (
          ( n mod p ) = ( m mod p )
          ->
          p || if ( m <_ n , ( n - m ) , 0 )
        )
      )
  $.
$}
