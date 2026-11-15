$(
  Statement-only formalization of the Logipedia corpus artifact logic.trans_eq
  (logipedia__metamath__logic.trans_eq), catalog title "logic.trans_eq":
  transitivity of the module's opaque polymorphic equality predicate for every
  three elements of every type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. The genuine SetMM set variable h represents the arbitrary
  source type A, and the restricted quantifiers x e. h, y e. h, and z e. h
  preserve the typed element binders. The nested implications therefore state
  exactly that LogLogicEq h x y and LogLogicEq h y z entail
  LogLogicEq h x z.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq h x y ) $.

${
  $d h x y z $.

  logipedia-logic-trans-eq $a |-
    A. h
      A. x e. h
        A. y e. h
          A. z e. h
            (
              ( LogLogicEq h x y )
              ->
              (
                ( LogLogicEq h y z )
                ->
                ( LogLogicEq h x z )
              )
            )
  $.
$}
