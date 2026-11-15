$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_times (logipedia__metamath__nat.eq_times), catalog title
  "nat.eq_times": for every natural number, times at that number is Leibniz
  equal to filter_nat_type applied to times_body at the same number, as
  functions from naturals to naturals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogTimes and LogTimesBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to results
  of type NN0 -> NN0, with type

    (NN0 -> NN0 -> NN0) -> NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. A predicate on the unary-function carrier is
  represented extensionally by a subset p of that carrier. Universal
  transport of membership from times n to the filtered times_body value is
  exactly the source definition of leibniz.leibniz at the function type.
  Every declaration introduced by this artifact is an unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

$c
  LogTimes LogTimesBody LogFilterNatTypeNat
  LogNatUnaryFunction LogNatBinaryFunction
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

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  $d n p $.

  logipedia-nat-eq-times $a |-
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
          A. p e. ~P ( LogNatUnaryFunction )
            (
              ( ( ( LogTimes ) ` n ) e. p )
              ->
              (
                (
                  (
                    ( LogFilterNatTypeNat )
                    `
                    ( LogTimesBody )
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
