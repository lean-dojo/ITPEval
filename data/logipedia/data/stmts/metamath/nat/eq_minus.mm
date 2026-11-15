$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_minus (logipedia__metamath__nat.eq_minus), catalog title
  "nat.eq_minus": for every natural number, minus at that number is Leibniz
  equal to filter_nat_type applied to minus_body at the same number, as
  functions from naturals to naturals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogMinus and LogMinusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to results
  of type NN0 -> NN0, with type

    (NN0 -> NN0 -> NN0) -> NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. A predicate on the unary-function carrier is
  represented extensionally by a subset p of that carrier. Universal
  transport of membership from minus n to the filtered minus_body value is
  exactly the source definition of leibniz.leibniz at the function type.
  Every declaration introduced by this artifact is an unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

$c
  LogMinus LogMinusBody LogFilterNatTypeNat
  LogNatUnaryFunction LogNatBinaryFunction
$.

log-minus-syntax $a class ( LogMinus ) $.
log-minus-body-syntax $a class ( LogMinusBody ) $.
log-filter-nat-type-nat-syntax $a
  class ( LogFilterNatTypeNat )
$.
log-nat-unary-function-syntax $a
  class ( LogNatUnaryFunction )
$.
log-nat-binary-function-syntax $a
  class ( LogNatBinaryFunction )
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  $d n p $.

  logipedia-nat-eq-minus $a |-
    (
      (
        ( LogMinus ) e. ( LogNatBinaryFunction )
        /\
        ( LogMinusBody ) e. ( LogNatBinaryFunction )
      )
      /\
      (
        ( LogFilterNatTypeNat ) e.
          (
            ( LogNatBinaryFunction )
            ^m
            ( LogNatBinaryFunction )
          )
        /\
        A. n e. NN0
          A. p e. ~P ( LogNatUnaryFunction )
            (
              ( ( ( LogMinus ) ` n ) e. p )
              ->
              (
                (
                  (
                    ( LogFilterNatTypeNat )
                    `
                    ( LogMinusBody )
                  )
                  `
                  n
                )
                e.
                p
              )
            )
      )
    )
  $.
$}
