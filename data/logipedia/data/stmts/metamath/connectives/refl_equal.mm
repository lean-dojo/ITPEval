$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.refl_equal, catalog title "connectives.refl_equal": reflexivity
  of the module's opaque polymorphic equality relation for every element of
  every type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source type A is represented by the set-level carrier h, and
  x is bounded to h. LogConnectivesEqual h x x represents the opaque source
  proposition connectives.equal A x x; its first $a declaration supplies only
  wff syntax. The final $a declaration is the native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesEqual $.

logipedia-connectives-equal-syntax $a wff
  LogConnectivesEqual h x y
$.

logipedia-connectives-refl-equal $a |-
  A. h A. x e. h LogConnectivesEqual h x x
$.
