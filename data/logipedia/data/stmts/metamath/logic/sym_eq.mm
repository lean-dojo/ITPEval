$(
  Statement-only formalization of the Logipedia corpus artifact logic.sym_eq
  (logipedia__metamath__logic.sym_eq), catalog title "logic.sym_eq": symmetry
  of the module's opaque polymorphic equality predicate for every pair of
  elements of every type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. The genuine SetMM set variable h represents the arbitrary
  source type A, and the restricted quantifiers x e. h and y e. h preserve the
  typed element binders. The implication therefore states exactly that
  LogLogicEq h x y entails LogLogicEq h y x.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq h x y ) $.

${
  $d h x y $.

  logipedia-logic-sym-eq $a |-
    A. h
      A. x e. h
        A. y e. h
          (
            ( LogLogicEq h x y )
            ->
            ( LogLogicEq h y x )
          )
  $.
$}
