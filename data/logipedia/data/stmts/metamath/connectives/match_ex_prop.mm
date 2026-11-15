$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.match_ex_prop, catalog title "connectives.match_ex_prop": the
  elimination principle for the module's opaque polymorphic existential
  proposition constructor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source type A is represented by the set-level carrier h. A
  source predicate P : A -> Prop is represented extensionally by an arbitrary
  subset p of h, while x is bounded to h. LogConnectivesEx h p represents the
  opaque source proposition connectives.ex A P; its first $a declaration
  supplies only wff syntax. Metamath's wff metavariable ch represents the
  arbitrary source proposition return. The final $a declaration preserves the
  assumption that every P-witness implies return and concludes that the opaque
  existential proposition implies return; it is the native unproved statement
  encoding, and this database contains no $p proof declaration.
$)

$c LogConnectivesEx $.

logipedia-connectives-ex-syntax $a wff
  LogConnectivesEx h p
$.

${
  $d h p $.
  $d h x $.
  $d p x $.
  $d ch x $.

  logipedia-connectives-match-ex-prop $a |-
    A. h A. p e. ~P h
      (
        A. x e. h ( x e. p -> ch )
        ->
        ( LogConnectivesEx h p -> ch )
      )
  $.
$}
