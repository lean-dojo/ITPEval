$(
  Statement-only formalization of the Logipedia corpus artifact
  cong.mod_times, catalog title "cong.mod_times": reducing a product of
  natural numbers modulo a positive natural modulus is unchanged when each
  factor is first reduced modulo that modulus. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. Under the source assumption that
  p is positive, mod is the natural-number remainder operation in both the
  source and this rendering. The declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d n m p $.

  logipedia-cong-mod-times $a |-
    A. n e. NN0 A. m e. NN0 A. p e. NN0
      (
        0 < p
        ->
        ( ( n x. m ) mod p )
        =
        ( ( ( n mod p ) x. ( m mod p ) ) mod p )
      )
  $.
$}
