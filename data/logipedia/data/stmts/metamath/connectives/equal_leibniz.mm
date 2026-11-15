$(
  Statement-only formalization of the Logipedia corpus artifact
  connectives.equal_leibniz, catalog title "connectives.equal_leibniz":
  the module's opaque polymorphic equality relation preserves every
  predicate from its left argument to its right argument. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source type A is represented by the set-level carrier h, and
  x and y are bounded to h. LogConnectivesEqual h x y represents the opaque
  source proposition connectives.equal A x y; its first $a declaration
  supplies only wff syntax. A source predicate P : A -> Prop is represented
  extensionally by an arbitrary subset p of h, so x e. p and y e. p encode
  P x and P y. The final $a declaration is the native unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c LogConnectivesEqual $.

logipedia-connectives-equal-syntax $a wff
  LogConnectivesEqual h x y
$.

${
  $d h p $.

  logipedia-connectives-equal-leibniz $a |-
    A. h A. x e. h A. y e. h
      (
        LogConnectivesEqual h x y
        ->
        A. p e. ~P h
          ( x e. p -> y e. p )
      )
  $.
$}
