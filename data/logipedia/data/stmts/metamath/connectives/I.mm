$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.I, catalog title "connectives.I": the module's distinguished
  opaque proposition connectives.True holds. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesTrue represents the source module parameter
  connectives.True, which is an opaque proposition rather than Metamath's
  built-in truth constant. The first $a declaration supplies only its wff
  syntax. The final $a declaration is the native unproved statement encoding;
  this database contains no $p proof declaration.
$)

$c LogConnectivesTrue $.

logipedia-connectives-true-syntax $a wff LogConnectivesTrue $.

logipedia-connectives-i $a |- LogConnectivesTrue $.
