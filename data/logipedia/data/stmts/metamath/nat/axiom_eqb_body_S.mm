$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_eqb_body_S (logipedia__metamath__nat.axiom_eqb_body_S),
  catalog title "nat.axiom_eqb_body_S": for every natural number n, the
  equality-test body at successor n equals the natural-number match function
  that returns false at zero and eqb n q at successor q. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  LogEqb and LogEqbBody represent the fixed source constants of type

    NN0 -> NN0 -> {0,1}.

  LogMatchNatBool is nat.match_nat_type specialized to the Boolean carrier,
  with source type

    {0,1} -> (NN0 -> {0,1}) -> NN0 -> {0,1}.

  The nested maps-to terms preserve the source lambdas over m and q, and
  n + 1 is the natural-number successor S n. Native SetMM equality is
  bidirectionally equivalent to connectives.equal here: equal_leibniz yields
  native equality, while native equality rewrites the right side to the left
  and refl_equal supplies source reflexivity. All declarations are unproved
  $a statement encodings; this database contains no $p proof declaration.
$)

$c
  LogEqb LogEqbBody LogMatchNatBool
  LogNatBoolUnaryFunction LogNatBoolBinaryFunction LogMatchNatBoolFunction
$.

log-eqb-syntax $a class ( LogEqb ) $.
log-eqb-body-syntax $a class ( LogEqbBody ) $.
log-match-nat-bool-syntax $a class ( LogMatchNatBool ) $.
log-nat-bool-unary-function-syntax $a
  class ( LogNatBoolUnaryFunction )
$.
log-nat-bool-binary-function-syntax $a
  class ( LogNatBoolBinaryFunction )
$.
log-match-nat-bool-function-syntax $a
  class ( LogMatchNatBoolFunction )
$.

log-nat-bool-unary-function-definition $a |-
  ( LogNatBoolUnaryFunction ) = ( { 0 , 1 } ^m NN0 )
$.

log-nat-bool-binary-function-definition $a |-
  ( LogNatBoolBinaryFunction ) =
    ( ( LogNatBoolUnaryFunction ) ^m NN0 )
$.

log-match-nat-bool-function-definition $a |-
  ( LogMatchNatBoolFunction ) =
    (
      (
        ( LogNatBoolUnaryFunction )
        ^m
        ( LogNatBoolUnaryFunction )
      )
      ^m
      { 0 , 1 }
    )
$.

${
  $d m n q $.

  logipedia-nat-axiom-eqb-body-s $a |-
    (
      (
        ( LogEqb ) e. ( LogNatBoolBinaryFunction )
        /\
        ( LogEqbBody ) e. ( LogNatBoolBinaryFunction )
      )
      /\
      (
        ( LogMatchNatBool ) e. ( LogMatchNatBoolFunction )
        /\
        A. n e. NN0
          (
            (
              m e. NN0 |->
                (
                  (
                    ( LogMatchNatBool ` 0 )
                    `
                    (
                      q e. NN0 |->
                        ( ( LogEqb ` n ) ` q )
                    )
                  )
                  `
                  m
                )
            ) e. ( LogNatBoolUnaryFunction )
            /\
            ( LogEqbBody ` ( n + 1 ) ) =
              (
                m e. NN0 |->
                  (
                    (
                      ( LogMatchNatBool ` 0 )
                      `
                      (
                        q e. NN0 |->
                          ( ( LogEqb ` n ) ` q )
                      )
                    )
                    `
                    m
                  )
              )
          )
      )
    )
  $.
$}
