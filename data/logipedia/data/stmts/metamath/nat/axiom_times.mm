$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_times (logipedia__metamath__nat.axiom_times), catalog title
  "nat.axiom_times": for every natural number, the source equality predicate
  relates times at that number to filter_nat_type applied to times_body at the
  same number, as functions from naturals to naturals. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  LogTimes and LogTimesBody represent the fixed source constants of type

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
  LogTimes LogTimesBody LogFilterNatTypeNat
  LogNatUnaryFunction LogNatBinaryFunction
  LogConnectivesEqual
$.

log-times-syntax $a class ( LogTimes ) $.
log-times-body-syntax $a class ( LogTimesBody ) $.
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
  logipedia-nat-axiom-times $a |-
    (
      (
        ( LogTimes ) e. ( LogNatBinaryFunction )
        /\
        ( LogTimesBody ) e. ( LogNatBinaryFunction )
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
            ( ( LogTimes ) ` n )
            (
              (
                ( LogFilterNatTypeNat )
                `
                ( LogTimesBody )
              )
              `
              n
            )
      )
    )
  $.
$}
