$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_div_O, catalog title "div_mod.eq_div_O": for natural numbers n
  and m with n less than m, the source natural quotient div n m equals zero.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The inline conditional is exactly
  div_mod.div: at divisor zero it returns n + 1, while at a positive divisor
  it is the usual natural quotient, represented by SetMM floor. The
  hypothesis n < m preserves the source assumption and in particular selects
  the positive-divisor branch. The declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-div-mod-eq-div-o $a |-
    A. n e. NN0 A. m e. NN0
      (
        n < m
        ->
        if (
          m = 0 ,
          ( n + 1 ) ,
          ( |_ ` ( n / m ) )
        )
        =
        0
      )
  $.
$}
