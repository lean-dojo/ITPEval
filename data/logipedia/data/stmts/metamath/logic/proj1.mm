$(
  Statement-only formalization of the Logipedia corpus artifact logic.proj1,
  catalog title "logic.proj1": the first-projection principle for the module's
  opaque binary conjunction on arbitrary propositions. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesAnd represents the source module parameter connectives.And.
  Its first $a declaration supplies only binary wff syntax. Metamath's wff
  metavariables ph and ps range schematically over the universally quantified
  source propositions A and B. The implication preserves the assumption
  connectives.And A B and conclusion A. The final $a declaration is the
  native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c LogConnectivesAnd $.

logipedia-connectives-and-syntax $a wff LogConnectivesAnd ph ps $.

logipedia-logic-proj1 $a |-
  ( LogConnectivesAnd ph ps -> ph )
$.
