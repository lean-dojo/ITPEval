$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.nmk, catalog title "connectives.nmk": the introduction
  principle for the module's opaque negation proposition, relative to its
  opaque false proposition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesFalse and LogConnectivesNot represent the source module
  parameters connectives.False and connectives.Not. The first two $a
  declarations supply only their wff syntax. Metamath's wff metavariable ph
  ranges schematically over the universally quantified source proposition A.
  The final $a declaration is the native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c LogConnectivesFalse LogConnectivesNot $.

logipedia-connectives-false-syntax $a wff LogConnectivesFalse $.
logipedia-connectives-not-syntax $a wff LogConnectivesNot ph $.

logipedia-connectives-nmk $a |-
  ( ( ph -> LogConnectivesFalse ) -> LogConnectivesNot ph )
$.
