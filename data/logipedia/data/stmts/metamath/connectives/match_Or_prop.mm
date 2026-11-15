$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.match_Or_prop, catalog title "connectives.match_Or_prop": the
  elimination principle for the module's opaque binary disjunction on
  arbitrary propositions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesOr represents the source module parameter connectives.Or.
  Its first $a declaration supplies only binary wff syntax. Metamath's wff
  metavariables ph, ps, and ch range schematically over the source
  propositions A, B, and return. The nested implications preserve the two
  branch assumptions A -> return and B -> return and the conclusion that
  connectives.Or A B implies return. The final $a declaration is the native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesOr $.

logipedia-connectives-or-syntax $a wff LogConnectivesOr ph ps $.

logipedia-connectives-match-or-prop $a |-
  ( ( ph -> ch )
    -> ( ( ps -> ch )
      -> ( LogConnectivesOr ph ps -> ch ) ) )
$.
