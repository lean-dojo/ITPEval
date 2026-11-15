$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.eq_exp (logipedia__metamath__exp.eq_exp), catalog title "exp.eq_exp":
  for every pair of natural numbers, exp at that pair is Leibniz equal to
  filter_nat_type applied to exp_body at the same pair. This file contains
  no proof.
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
  of membership from exp n m to the filtered exp_body value is exactly the
  source definition of leibniz.leibniz at nat.nat. The source signature fixes
  the constants' function types; those typing facts are not added as theorem
  conjuncts. Every declaration is an unproved $a statement encoding; this
  database contains no $p proof declaration.
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

  logipedia-exp-eq-exp $a |-
    A. n e. NN0 A. m e. NN0
      A. p e. ~P NN0
        (
          ( ( ( LogExp ` n ) ` m ) e. p )
          ->
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
        )
  $.
$}
