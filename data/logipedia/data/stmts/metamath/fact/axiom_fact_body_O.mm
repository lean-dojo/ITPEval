$(
  Statement-only formalization of the Logipedia corpus artifact
  fact.axiom_fact_body_O (logipedia__metamath__fact.axiom_fact_body_O),
  catalog title "fact.axiom_fact_body_O": the factorial body at zero equals
  the successor of zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogFactBody represents the fixed source constant of type

    NN0 -> NN0.

  The numeral 1 is the SetMM natural number corresponding to the source term
  nat.S nat.O. LogConnectivesEqual remains the source's opaque polymorphic
  equality predicate, specialized here to NN0. All declarations are unproved
  $a statement encodings; this database contains no $p proof declaration.
$)

$c LogFactBody LogNatUnaryFunction LogConnectivesEqual $.

log-fact-body-syntax $a class ( LogFactBody ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

logipedia-fact-axiom-fact-body-o $a |-
  LogConnectivesEqual NN0 ( ( LogFactBody ) ` 0 ) 1
$.
