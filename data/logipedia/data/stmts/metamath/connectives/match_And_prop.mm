$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.match_And_prop, catalog title "connectives.match_And_prop": the
  elimination principle for the module's opaque binary conjunction on
  arbitrary propositions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesAnd represents the source module parameter connectives.And.
  Its first $a declaration supplies only binary wff syntax. Metamath's wff
  metavariables ph, ps, and ch range schematically over the source
  propositions A, B, and return. The nested implications preserve the
  curried assumption A -> B -> return and the conclusion that
  connectives.And A B implies return. The final $a declaration is the native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesAnd $.

logipedia-connectives-and-syntax $a wff LogConnectivesAnd ph ps $.

logipedia-connectives-match-and-prop $a |-
  ( ( ph -> ( ps -> ch ) )
    -> ( LogConnectivesAnd ph ps -> ch ) )
$.
