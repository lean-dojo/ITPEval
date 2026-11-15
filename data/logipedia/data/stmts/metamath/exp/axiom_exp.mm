$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.axiom_exp (logipedia__metamath__exp.axiom_exp), catalog title
  "exp.axiom_exp": for every pair of natural numbers, exp at that pair
  equals filter_nat_type applied to exp_body at the same pair. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogExp and LogExpBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to natural
  results, with type

    (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode those
  curried function spaces. Native SetMM equality represents the source
  connectives.equal relation at the natural-number type. All declarations
  are unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c
  LogExp LogExpBody LogFilterNatTypeNat
  LogNatUnaryFunction LogNatBinaryFunction
$.

log-exp-syntax $a class ( LogExp ) $.
log-exp-body-syntax $a class ( LogExpBody ) $.
log-filter-nat-type-nat-syntax $a class ( LogFilterNatTypeNat ) $.
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
  $d m n $.

  logipedia-exp-axiom-exp $a |-
    (
      (
        ( LogExp ) e. ( LogNatBinaryFunction )
        /\
        ( LogExpBody ) e. ( LogNatBinaryFunction )
      )
      /\
      (
        ( LogFilterNatTypeNat ) e.
          (
            ( LogNatUnaryFunction )
            ^m
            ( LogNatUnaryFunction )
          )
        /\
        A. n e. NN0 A. m e. NN0
          (
            ( ( LogExp ` n ) ` m )
            =
            (
              (
                ( LogFilterNatTypeNat )
                `
                ( LogExpBody ` n )
              )
              `
              m
            )
          )
      )
    )
  $.
$}
