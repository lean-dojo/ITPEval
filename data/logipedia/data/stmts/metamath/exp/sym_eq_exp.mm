$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.sym_eq_exp (logipedia__metamath__exp.sym_eq_exp), catalog title
  "exp.sym_eq_exp": for every pair of natural numbers, filter_nat_type
  applied to exp_body is Leibniz equal to exp at the same pair. This file
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
  curried function spaces. A predicate on the natural-number carrier is
  represented extensionally by a subset p of NN0. Thus universal transport
  of membership from the filtered exp_body value to exp n m is exactly the
  source definition of leibniz.leibniz at nat.nat. Every declaration is an
  unproved $a statement encoding; this database contains no $p proof
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
  $d m n p $.

  logipedia-exp-sym-eq-exp $a |-
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
          A. p e. ~P NN0
            (
              (
                (
                  (
                    ( LogFilterNatTypeNat )
                    `
                    ( LogExpBody ` n )
                  )
                  `
                  m
                )
                e.
                p
              )
              ->
              ( ( ( LogExp ` n ) ` m ) e. p )
            )
      )
    )
  $.
$}
