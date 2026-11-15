$(
  Statement-only formalization of the Logipedia corpus artifact logic.absurd,
  catalog title "logic.absurd": for every proposition, that proposition
  together with its opaque module negation entails the module's opaque false
  proposition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesFalse and LogConnectivesNot represent the source module
  parameters connectives.False and connectives.Not. The first two $a
  declarations supply only their wff syntax. Metamath's wff metavariable ph
  ranges schematically over the universally quantified source proposition A,
  and the nested implications preserve the curried assumptions
  A -> connectives.Not A -> connectives.False. The final $a declaration is
  the native unproved statement encoding; this database contains no $p proof
  declaration.
$)

$c LogConnectivesFalse LogConnectivesNot $.

logipedia-connectives-false-syntax $a wff LogConnectivesFalse $.
logipedia-connectives-not-syntax $a wff LogConnectivesNot ph $.

logipedia-logic-absurd $a |-
  ( ph -> ( LogConnectivesNot ph -> LogConnectivesFalse ) )
$.
