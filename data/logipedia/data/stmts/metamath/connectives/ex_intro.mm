$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.ex_intro, catalog title "connectives.ex_intro": the introduction
  principle for the module's opaque polymorphic existential proposition
  constructor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source type A is represented by the set-level carrier h. A
  source predicate P : A -> Prop is represented extensionally by an arbitrary
  subset p of h, and x is bounded to h. LogConnectivesEx h p represents the
  opaque source proposition connectives.ex A P; its first $a declaration
  supplies only wff syntax. The final $a declaration is the native unproved
  statement encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesEx $.

logipedia-connectives-ex-syntax $a wff
  LogConnectivesEx h p
$.

${
  $d h p $.

  logipedia-connectives-ex-intro $a |-
    A. h A. p e. ~P h A. x e. h
      ( x e. p -> LogConnectivesEx h p )
  $.
$}
