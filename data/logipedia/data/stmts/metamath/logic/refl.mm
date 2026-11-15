$(
  Statement-only formalization of the Logipedia corpus artifact logic.refl
  (logipedia__metamath__logic.refl), catalog title "logic.refl": reflexivity
  of the module's opaque polymorphic equality predicate for every element of
  every type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. The genuine SetMM set variable h represents the arbitrary
  source type A, and the restricted quantifier x e. h preserves the typed
  element binder. Thus LogLogicEq h x x represents logic.eq A x x for every
  type A and every x : A.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq h x y ) $.

${
  $d h x $.

  logipedia-logic-refl $a |-
    A. h
      A. x e. h
        ( LogLogicEq h x x )
  $.
$}
