$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_minus (logipedia__metamath__nat.axiom_minus), catalog title
  "nat.axiom_minus": for every natural number, the source equality predicate
  relates minus at that number to filter_nat_type applied to minus_body at the
  same number, as functions from naturals to naturals. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  LogMinus and LogMinusBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to results
  of type NN0 -> NN0, with type

    (NN0 -> NN0 -> NN0) -> NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. LogConnectivesEqual remains the source's opaque
  polymorphic equality predicate, specialized in the final statement to the
  full function type NN0 -> NN0. The membership conjuncts preserve the source
  declarations' types. All declarations are unproved $a statement encodings;
  this database contains no $p proof declaration.
$)

$c
  LogMinus LogMinusBody LogFilterNatTypeNat
  LogNatUnaryFunction LogNatBinaryFunction
  LogConnectivesEqual
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
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  logipedia-nat-axiom-minus $a |-
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
          LogConnectivesEqual
            ( LogNatUnaryFunction )
            ( ( LogMinus ) ` n )
            (
              (
                ( LogFilterNatTypeNat )
                `
                ( LogMinusBody )
              )
              `
              n
            )
      )
    )
  $.
$}
