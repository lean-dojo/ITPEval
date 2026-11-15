$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.or_intror, catalog title "connectives.or_intror": the right
  introduction principle for the module's opaque binary disjunction on
  arbitrary propositions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesOr represents the source module parameter connectives.Or.
  Its first $a declaration supplies only binary wff syntax. Metamath's wff
  metavariables ph and ps range schematically over the source propositions A
  and B, and the implication preserves the assumption B and conclusion
  connectives.Or A B. The final $a declaration is the native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesOr $.

logipedia-connectives-or-syntax $a wff LogConnectivesOr ph ps $.

logipedia-connectives-or-intror $a |-
  ( ps -> LogConnectivesOr ph ps )
$.
