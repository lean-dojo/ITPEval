$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_times_div_minus_mod
  (logipedia__metamath__div_mod.eq_times_div_minus_mod), catalog title
  "div_mod.eq_times_div_minus_mod": for all natural numbers a and b, the
  source quotient of a by b times b equals a minus the source remainder.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The quotient and remainder
  conditionals are exactly div_mod.div and div_mod.mod: at divisor zero they
  return a + 1 and a respectively, while at a positive divisor they are the
  usual natural quotient and remainder. SetMM floor represents the positive-
  divisor quotient. The outer conditional on the right is exactly truncated
  natural subtraction.

  The declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d a b $.

  logipedia-div-mod-eq-times-div-minus-mod $a |-
    A. a e. NN0 A. b e. NN0
      (
        (
          if (
            b = 0 ,
            ( a + 1 ) ,
            ( |_ ` ( a / b ) )
          )
          x. b
        )
        =
        if (
          if (
            b = 0 ,
            a ,
            ( a mod b )
          ) <_ a ,
          (
            a -
            if (
              b = 0 ,
              a ,
              ( a mod b )
            )
          ) ,
          0
        )
      )
  $.
$}
