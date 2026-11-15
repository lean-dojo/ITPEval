$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_minus_body_S (logipedia__metamath__nat.eq_minus_body_S), catalog
  title "nat.eq_minus_body_S": for every natural number n, the subtraction
  body at successor n is Leibniz equal, as a function on natural numbers, to
  the natural-number match function with successor n as its zero branch and
  minus n q as its successor branch. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogMinus and LogMinusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogMatchNatNat represents nat.match_nat_type specialized to natural-number
  results, with source type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried function spaces. The nested maps-to terms preserve the source
  lambdas over m and q, and n + 1 is the natural-number successor S n. A
  predicate on the unary-function carrier is represented extensionally by a
  subset p of that carrier. Universal transport of membership from
  minus_body (S n) to the matcher function is exactly the source definition
  of leibniz.leibniz at the function type. Every assertion introduced by this
  artifact is an unproved $a statement encoding; this artifact introduces no
  $p proof declaration.
$)

$c
  LogMinus LogMinusBody LogMatchNatNat
  LogNatUnaryFunction LogNatBinaryFunction LogMatchNatNatFunction
$.

log-minus-syntax $a class ( LogMinus ) $.
log-minus-body-syntax $a class ( LogMinusBody ) $.
log-match-nat-nat-syntax $a class ( LogMatchNatNat ) $.
log-nat-unary-function-syntax $a
  class ( LogNatUnaryFunction )
$.
log-nat-binary-function-syntax $a
  class ( LogNatBinaryFunction )
$.
log-match-nat-nat-function-syntax $a
  class ( LogMatchNatNatFunction )
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

log-match-nat-nat-function-definition $a |-
  ( LogMatchNatNatFunction ) =
    (
      (
        ( LogNatUnaryFunction )
        ^m
        ( LogNatUnaryFunction )
      )
      ^m
      NN0
    )
$.

${
  $d m n p q $.

  logipedia-nat-eq-minus-body-s $a |-
    (
      (
        ( LogMinus ) e. ( LogNatBinaryFunction )
        /\
        ( LogMinusBody ) e. ( LogNatBinaryFunction )
      )
      /\
      (
        ( LogMatchNatNat ) e. ( LogMatchNatNatFunction )
        /\
        A. n e. NN0
          (
            (
              m e. NN0 |->
                (
                  (
                    ( LogMatchNatNat ` ( n + 1 ) )
                    `
                    (
                      q e. NN0 |->
                        ( ( LogMinus ` n ) ` q )
                    )
                  )
                  `
                  m
                )
            ) e. ( LogNatUnaryFunction )
            /\
            A. p e. ~P ( LogNatUnaryFunction )
              (
                ( ( LogMinusBody ` ( n + 1 ) ) e. p )
                ->
                (
                  (
                    m e. NN0 |->
                      (
                        (
                          ( LogMatchNatNat ` ( n + 1 ) )
                          `
                          (
                            q e. NN0 |->
                              ( ( LogMinus ` n ) ` q )
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
