$(
  Statement-only formalization of the Logipedia corpus artifact cong.mod_mod,
  catalog title "cong.mod_mod": taking the remainder of a natural number
  modulo a positive natural modulus is idempotent. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. Under the source assumption that
  p is positive, mod is the natural-number remainder operation in both the
  source and this rendering. The declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d n p $.

  logipedia-cong-mod-mod $a |-
    A. n e. NN0 A. p e. NN0
      (
        0 < p
        ->
        ( n mod p ) = ( ( n mod p ) mod p )
      )
  $.
$}
