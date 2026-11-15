$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_mod_spec_div_mod, catalog title
  "div_mod.div_mod_spec_div_mod": for natural numbers n and positive m, the
  source quotient and remainder satisfy the division-with-remainder
  specification. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source introduction and elimination declarations make
  div_mod_spec n m q r logically equivalent to

    r < m /\ n = (q x. m) + r.

  The two inline conditionals are exactly div_mod.div and div_mod.mod: at
  divisor zero they return n + 1 and n respectively, while at a positive
  divisor they are the usual natural quotient and remainder. Thus the final
  conjunction is a bidirectionally equivalent rendering of the source
  predicate with its original function arguments. The declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d m n $.

  logipedia-div-mod-div-mod-spec-div-mod $a |-
    A. n e. NN0 A. m e. NN0
      (
        0 < m
        ->
        (
          (
            if (
              m = 0 ,
              n ,
              ( n mod m )
            )
            < m
          )
          /\
          n =
            (
              (
                if (
                  m = 0 ,
                  ( n + 1 ) ,
                  ( |_ ` ( n / m ) )
                )
                x. m
              )
              +
              if (
                m = 0 ,
                n ,
                ( n mod m )
              )
            )
        )
      )
  $.
$}
