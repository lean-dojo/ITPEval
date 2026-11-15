$(
  Statement-only formalization of the Logipedia corpus artifact
  fact.eq_fact (logipedia__metamath__fact.eq_fact), catalog title
  "fact.eq_fact": for every natural number, fact at that number is Leibniz
  equal to filter_nat_type applied to fact_body at the same number. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogFact and LogFactBody represent the fixed source constants of type

    NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to natural
  results, with type

    (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction records that function space outside the benchmark
  proposition. A predicate on the natural-number carrier is represented
  extensionally by a subset p of NN0. Thus universal transport of membership
  from fact n to the filtered fact_body value is exactly the source definition
  of leibniz.leibniz at nat.nat. Every declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

$c
  LogFact LogFactBody LogFilterNatTypeNat LogNatUnaryFunction
$.

log-fact-syntax $a class ( LogFact ) $.
log-fact-body-syntax $a class ( LogFactBody ) $.
log-filter-nat-type-nat-syntax $a class ( LogFilterNatTypeNat ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

${
  $d n p $.

  logipedia-fact-eq-fact $a |-
    A. n e. NN0
      A. p e. ~P NN0
        (
          ( ( ( LogFact ) ` n ) e. p )
          ->
          (
            (
              (
                ( LogFilterNatTypeNat )
                `
                ( LogFactBody )
              )
              `
              n
            )
            e.
            p
          )
        )
  $.
$}
