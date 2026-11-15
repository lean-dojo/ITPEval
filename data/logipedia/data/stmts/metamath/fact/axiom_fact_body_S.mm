$(
  Statement-only formalization of the Logipedia corpus artifact
  fact.axiom_fact_body_S (logipedia__metamath__fact.axiom_fact_body_S),
  catalog title "fact.axiom_fact_body_S": for every natural number n, the
  source equality predicate relates the factorial body at the successor of n
  to fact at n multiplied by that successor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogFact and LogFactBody represent the fixed source constants of type

    NN0 -> NN0.

  LogNatUnaryFunction records that function space outside the benchmark
  proposition. SetMM's n + 1 is the source successor nat.S n, and SetMM
  multiplication preserves the source argument order nat.times (fact n)
  (nat.S n). LogConnectivesEqual remains the source's primitive type-indexed
  predicate. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c
  LogFact LogFactBody LogNatUnaryFunction LogConnectivesEqual
$.

log-fact-syntax $a class ( LogFact ) $.
log-fact-body-syntax $a class ( LogFactBody ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

${
  $d n q x y $.

  logipedia-fact-axiom-fact-body-s $a |-
    A. n e. NN0
      LogConnectivesEqual
        NN0
        ( ( LogFactBody ) ` ( n + 1 ) )
        ( ( ( LogFact ) ` n ) x. ( n + 1 ) )
  $.
$}
