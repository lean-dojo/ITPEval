$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.conj, catalog title "connectives.conj": the conjunction-
  introduction principle for the module's opaque binary conjunction on
  arbitrary propositions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesAnd represents the source module parameter connectives.And.
  Its first $a declaration supplies only binary wff syntax. Metamath's wff
  metavariables ph and ps range schematically over the source propositions A
  and B, and the nested implications preserve the curried assumptions
  A -> B -> connectives.And A B. The final $a declaration is the native
  unproved statement encoding; this artifact contains no $p proof declaration.
$)

$c LogConnectivesAnd $.

logipedia-connectives-and-syntax $a wff LogConnectivesAnd ph ps $.

logipedia-connectives-conj $a |-
  ( ph -> ( ps -> LogConnectivesAnd ph ps ) )
$.
