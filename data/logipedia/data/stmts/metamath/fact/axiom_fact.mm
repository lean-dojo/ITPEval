$(
  Statement-only formalization of the Logipedia corpus artifact
  fact.axiom_fact (logipedia__metamath__fact.axiom_fact), catalog title
  "fact.axiom_fact": for every natural number, the source equality predicate
  relates fact at that number to filter_nat_type applied to fact_body at the
  same number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogFact and LogFactBody represent the fixed source constants of type

    NN0 -> NN0.

  LogFilterNatTypeNat represents nat.filter_nat_type specialized to natural
  results, with type

    (NN0 -> NN0) -> NN0 -> NN0.

  LogConnectivesEqual remains the source's opaque polymorphic equality
  predicate, specialized in the final statement to the carrier NN0. The
  source declarations' types are represented by the surrounding syntax and
  function-space declarations, not by extra conjuncts in the benchmark
  proposition. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c
  LogFact LogFactBody LogFilterNatTypeNat
  LogNatUnaryFunction LogConnectivesEqual
$.

log-fact-syntax $a class ( LogFact ) $.
log-fact-body-syntax $a class ( LogFactBody ) $.
log-filter-nat-type-nat-syntax $a class ( LogFilterNatTypeNat ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

${
  logipedia-fact-axiom-fact $a |-
    A. n e. NN0
      LogConnectivesEqual
        NN0
        ( ( LogFact ) ` n )
        (
          (
            ( LogFilterNatTypeNat )
            `
            ( LogFactBody )
          )
          `
          n
        )
  $.
$}
