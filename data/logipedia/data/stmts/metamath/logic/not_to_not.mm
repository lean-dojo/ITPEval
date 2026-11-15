$(
  Statement-only formalization of the Logipedia corpus artifact
  logic.not_to_not, catalog title "logic.not_to_not": contraposition for the
  module's opaque negation, sending an implication from A to B and a negation
  of B to a negation of A. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesNot represents the source module parameter connectives.Not.
  Its first $a declaration supplies only unary wff syntax. Metamath's wff
  metavariables ph and ps range schematically over the universally quantified
  source propositions A and B. The nested implications preserve the curried
  statement (A -> B) -> connectives.Not B -> connectives.Not A. The final $a
  declaration is the native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogConnectivesNot $.

logipedia-connectives-not-syntax $a wff LogConnectivesNot ph $.

logipedia-logic-not-to-not $a |-
  ( ( ph -> ps ) -> ( LogConnectivesNot ps -> LogConnectivesNot ph ) )
$.
