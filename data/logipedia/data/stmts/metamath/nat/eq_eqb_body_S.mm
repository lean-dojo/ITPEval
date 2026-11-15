$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_eqb_body_S (logipedia__metamath__nat.eq_eqb_body_S), catalog title
  "nat.eq_eqb_body_S": for every natural number n, the equality-test body at
  successor n is Leibniz equal, as a function from natural numbers to
  Booleans, to the natural-number match function that returns false at zero
  and eqb n q at successor q. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogEqb and LogEqbBody represent the fixed source constants of type

    NN0 -> NN0 -> {0,1}.

  LogMatchNatBool is nat.match_nat_type specialized to the Boolean carrier,
  with source type

    {0,1} -> (NN0 -> {0,1}) -> NN0 -> {0,1}.

  The nested maps-to terms preserve the source lambdas over m and q, and
  n + 1 is the natural-number successor S n. A predicate on the unary-function
  carrier is represented extensionally by a subset p of that carrier.
  Universal transport of membership from eqb_body (S n) to the matcher
  function is exactly the source definition of leibniz.leibniz at the
  function type. Every declaration is an unproved $a statement encoding;
  this artifact introduces no $p proof declaration.
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
  $d m n p q $.

  logipedia-nat-eq-eqb-body-s $a |-
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
            A. p e. ~P ( LogNatBoolUnaryFunction )
              (
                ( ( LogEqbBody ` ( n + 1 ) ) e. p )
                ->
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
                  )
                  e.
                  p
                )
              )
          )
      )
    )
  $.
$}
