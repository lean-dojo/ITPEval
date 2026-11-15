$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_plus (logipedia__metamath__nat.eq_plus), catalog title
  "nat.eq_plus": for every natural number, plus at that number is Leibniz
  equal to filter_nat_type applied to plus_body at the same number, as
  functions from naturals to naturals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlus and LogPlusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to results
  of type NN0 -> NN0, with type

    (NN0 -> NN0 -> NN0) -> NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. A predicate on the unary-function carrier is
  represented extensionally by a subset p of that carrier. Universal
  transport of membership from plus n to the filtered plus_body value is
  exactly the source definition of leibniz.leibniz at the function type.
  Every declaration introduced by this artifact is an unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

$c
  LogPlus LogPlusBody LogFilterNatTypeNat
  LogNatUnaryFunction LogNatBinaryFunction
$.

log-plus-syntax $a class ( LogPlus ) $.
log-plus-body-syntax $a class ( LogPlusBody ) $.
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

  logipedia-nat-eq-plus $a |-
    (
      (
        ( LogPlus ) e. ( LogNatBinaryFunction )
        /\
        ( LogPlusBody ) e. ( LogNatBinaryFunction )
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
              ( ( ( LogPlus ) ` n ) e. p )
              ->
              (
                (
                  (
                    ( LogFilterNatTypeNat )
                    `
                    ( LogPlusBody )
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
