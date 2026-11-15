$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_eqb_body_O (logipedia__metamath__nat.axiom_eqb_body_O),
  catalog title "nat.axiom_eqb_body_O": the equality-test body at zero equals
  the natural-number match function that returns true at zero and false at
  every successor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogEqbBody represents the fixed source constant of type

    NN0 -> NN0 -> {0,1}.

  LogMatchNatBool is nat.match_nat_type specialized to the Boolean carrier,
  with source type

    {0,1} -> (NN0 -> {0,1}) -> NN0 -> {0,1}.

  The nested maps-to terms preserve both source lambdas, including the
  ignored predecessor argument in the constant-false successor branch.
  Native SetMM equality is bidirectionally equivalent to connectives.equal
  here: equal_leibniz yields native equality, while native equality rewrites
  the right side to the left and refl_equal supplies source reflexivity.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c
  LogEqbBody LogMatchNatBool
  LogNatBoolUnaryFunction LogNatBoolBinaryFunction LogMatchNatBoolFunction
$.

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
  $d m q $.

  logipedia-nat-axiom-eqb-body-o $a |-
    (
      (
        ( LogEqbBody ) e. ( LogNatBoolBinaryFunction )
        /\
        ( LogMatchNatBool ) e. ( LogMatchNatBoolFunction )
      )
      /\
      (
        (
          m e. NN0 |->
            (
              (
                ( LogMatchNatBool ` 1 )
                `
                ( q e. NN0 |-> 0 )
              )
              `
              m
            )
        ) e. ( LogNatBoolUnaryFunction )
        /\
        ( LogEqbBody ` 0 ) =
          (
            m e. NN0 |->
              (
                (
                  ( LogMatchNatBool ` 1 )
                  `
                  ( q e. NN0 |-> 0 )
                )
                `
                m
              )
          )
      )
    )
  $.
$}
