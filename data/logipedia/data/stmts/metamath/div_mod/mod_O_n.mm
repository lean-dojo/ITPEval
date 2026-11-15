$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.mod_O_n, catalog title "div_mod.mod_O_n": for every natural number
  n, the source remainder of zero modulo n is zero. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The inline conditional is exactly
  div_mod.mod: at divisor zero it returns the dividend, while at a positive
  divisor it is the usual natural remainder. The declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

${
  logipedia-div-mod-mod-o-n $a |-
    A. n e. NN0
      if (
        n = 0 ,
        0 ,
        ( 0 mod n )
      )
      =
      0
  $.
$}
