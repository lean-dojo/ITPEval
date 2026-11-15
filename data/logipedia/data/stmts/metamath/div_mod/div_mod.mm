$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.div_mod, catalog title "div_mod.div_mod": every pair of natural
  numbers satisfies the source's total division-with-remainder identity.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain. The two inline conditionals are
  exactly div_mod.div and div_mod.mod: at divisor zero they return n + 1 and
  n respectively, while at a positive divisor they are the usual natural
  quotient and remainder. SetMM floor therefore represents the positive-
  divisor quotient without changing the source's zero-divisor behavior.
  The declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-div-mod-div-mod $a |-
    A. n e. NN0 A. m e. NN0
      n
      =
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
  $.
$}
