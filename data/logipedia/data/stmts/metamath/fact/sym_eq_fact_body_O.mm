$(
  Statement-only formalization of the Logipedia corpus artifact
  fact.sym_eq_fact_body_O (logipedia__metamath__fact.sym_eq_fact_body_O),
  catalog title "fact.sym_eq_fact_body_O": the successor of zero is Leibniz
  equal to the factorial body at zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogFactBody represents the fixed source constant of type

    NN0 -> NN0.

  LogNatUnaryFunction records that function space outside the benchmark
  proposition. The numeral 1 is the SetMM natural number corresponding to the
  source term nat.S nat.O. A predicate on the natural-number carrier is
  represented extensionally by a subset p of NN0. Thus universal transport of
  membership from 1 to fact_body 0 is exactly the source definition of
  leibniz.leibniz at nat.nat. Every declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

$c LogFactBody LogNatUnaryFunction $.

log-fact-body-syntax $a class ( LogFactBody ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

logipedia-fact-sym-eq-fact-body-o $a |-
  A. p e. ~P NN0
    (
      ( 1 e. p )
      ->
      ( ( ( LogFactBody ) ` 0 ) e. p )
    )
$.
