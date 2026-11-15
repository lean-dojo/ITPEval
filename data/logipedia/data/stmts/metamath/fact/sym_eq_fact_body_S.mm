$(
  Statement-only formalization of the Logipedia corpus artifact
  fact.sym_eq_fact_body_S (logipedia__metamath__fact.sym_eq_fact_body_S),
  catalog title "fact.sym_eq_fact_body_S": for every natural number n, fact
  at n multiplied by the successor of n is Leibniz equal to the factorial
  body at that successor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogFact and LogFactBody represent the fixed source constants of type

    NN0 -> NN0.

  LogNatUnaryFunction records that function space outside the benchmark
  proposition. SetMM's n + 1 is the source successor nat.S n, and SetMM
  multiplication preserves the source argument order nat.times (fact n)
  (nat.S n). A predicate on the natural-number carrier is represented
  extensionally by a subset p of NN0. Thus universal transport of membership
  from fact n * S n to fact_body (S n) is exactly the source definition of
  leibniz.leibniz at nat.nat. Every declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

$c LogFact LogFactBody LogNatUnaryFunction $.

log-fact-syntax $a class ( LogFact ) $.
log-fact-body-syntax $a class ( LogFactBody ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

${
  $d n p $.

  logipedia-fact-sym-eq-fact-body-s $a |-
    A. n e. NN0
      A. p e. ~P NN0
        (
          ( ( ( ( LogFact ) ` n ) x. ( n + 1 ) ) e. p )
          ->
          ( ( ( LogFactBody ) ` ( n + 1 ) ) e. p )
        )
  $.
$}
