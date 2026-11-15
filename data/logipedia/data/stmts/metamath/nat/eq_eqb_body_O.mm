$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_eqb_body_O (logipedia__metamath__nat.eq_eqb_body_O), catalog title
  "nat.eq_eqb_body_O": the equality-test body at zero is Leibniz equal, as a
  function from natural numbers to Booleans, to the natural-number match
  function that returns true at zero and false at every successor. This file
  contains no proof.
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
  A predicate on the unary-function carrier is represented extensionally by
  a subset p of that carrier. Universal transport of membership from
  eqb_body O to the matcher function is exactly the source definition of
  leibniz.leibniz at the function type. The source signature fixes the types
  of LogEqbBody and LogMatchNatBool; those typing facts are context, not
  extra conjuncts in the translated theorem. Every declaration is an
  unproved $a statement encoding; this artifact introduces no $p proof
  declaration.
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
  $d m p q $.

  logipedia-nat-eq-eqb-body-o $a |-
    A. p e. ~P ( LogNatBoolUnaryFunction )
      (
        ( ( LogEqbBody ` 0 ) e. p )
        ->
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
          )
          e.
          p
        )
      )
  $.
$}
