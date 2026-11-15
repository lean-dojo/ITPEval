$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.or_introl, catalog title "connectives.or_introl": the left
  introduction principle for the module's opaque binary disjunction on
  arbitrary propositions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesOr represents the source module parameter connectives.Or.
  Its first $a declaration supplies only binary wff syntax. Metamath's wff
  metavariables ph and ps range schematically over the source propositions A
  and B, and the implication preserves the assumption A and conclusion
  connectives.Or A B. The final $a declaration is the native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesOr $.

logipedia-connectives-or-syntax $a wff LogConnectivesOr ph ps $.

logipedia-connectives-or-introl $a |-
  ( ph -> LogConnectivesOr ph ps )
$.
