$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_times (logipedia__metamath__nat.sym_eq_times), catalog title
  "nat.sym_eq_times": for every natural number, filter_nat_type applied to
  times_body at that number is Leibniz equal, as a unary natural-number
  function, to times at the same number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogTimes and LogTimesBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogFilterNatTypeUnary represents nat.filter_nat_type specialized to unary
  natural-number functions, with type

    (NN0 -> NN0 -> NN0) -> NN0 -> (NN0 -> NN0).

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. A predicate on the unary-function carrier is
  represented extensionally by a subset p of LogNatUnaryFunction. Thus
  universal transport of membership from the filtered times_body function to
  times n is exactly the source definition of leibniz.leibniz at type
  NN0 -> NN0. Every declaration is an unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c
  LogTimes LogTimesBody LogFilterNatTypeUnary
  LogNatUnaryFunction LogNatBinaryFunction
$.

log-times-syntax $a class ( LogTimes ) $.
log-times-body-syntax $a class ( LogTimesBody ) $.
log-filter-nat-type-unary-syntax $a class ( LogFilterNatTypeUnary ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  $d n p $.

  logipedia-nat-sym-eq-times $a |-
    (
      (
        ( LogTimes ) e. ( LogNatBinaryFunction )
        /\
        ( LogTimesBody ) e. ( LogNatBinaryFunction )
      )
      /\
      (
        ( LogFilterNatTypeUnary ) e.
          (
            ( LogNatBinaryFunction )
            ^m
            ( LogNatBinaryFunction )
          )
        /\
        A. n e. NN0
          A. p e. ~P ( LogNatUnaryFunction )
            (
              (
                (
                  ( LogFilterNatTypeUnary )
                  `
                  ( LogTimesBody )
                )
                `
                n
              )
              e.
              p
              ->
              ( ( ( LogTimes ) ` n ) e. p )
            )
      )
    )
  $.
$}
