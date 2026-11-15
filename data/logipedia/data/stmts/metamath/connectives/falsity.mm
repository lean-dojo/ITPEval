$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.falsity, catalog title "connectives.falsity": from the module's
  opaque false proposition, every proposition follows. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  LogConnectivesFalse represents the source module parameter
  connectives.False, which is an opaque proposition rather than Metamath's
  built-in falsum. The first $a declaration supplies only its wff syntax.
  Metamath's wff metavariable ph ranges schematically over the universally
  quantified source proposition t. The final $a declaration is the native
  unproved statement encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesFalse $.

logipedia-connectives-false-syntax $a wff LogConnectivesFalse $.

logipedia-connectives-falsity $a |-
  ( LogConnectivesFalse -> ph )
$.
