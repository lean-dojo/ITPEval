$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_times, catalog title "div_mod.div_times": for natural numbers
  a and positive b, dividing a times b by b yields a. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The inline conditional is exactly
  div_mod.div on the dividend a x. b: at divisor zero it returns the
  successor ( a x. b ) + 1, while at a positive divisor it is the usual
  natural quotient, represented by SetMM floor. The hypothesis 0 < b
  preserves the source's positivity assumption. The declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d a b $.

  logipedia-div-mod-div-times $a |-
    A. a e. NN0 A. b e. NN0
      (
        0 < b
        ->
        if (
          b = 0 ,
          ( ( a x. b ) + 1 ) ,
          ( |_ ` ( ( a x. b ) / b ) )
        )
        =
        a
      )
  $.
$}
