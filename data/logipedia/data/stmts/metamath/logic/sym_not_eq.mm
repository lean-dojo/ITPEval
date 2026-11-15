$(
  Statement-only formalization of the Logipedia corpus artifact
  logic.sym_not_eq (logipedia__metamath__logic.sym_not_eq), catalog title
  "logic.sym_not_eq": symmetry of non-equality for every pair of elements of
  every type, using the module's opaque equality and negation predicates.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq and LogConnectivesNot represent the source module's opaque
  type-indexed equality predicate logic.eq and negation predicate
  connectives.Not. The genuine SetMM set variable h represents the arbitrary
  source type A, while the restricted quantifiers x e. h and y e. h preserve
  the typed element binders. The implication therefore states exactly that
  connectives.Not (logic.eq A x y) entails
  connectives.Not (logic.eq A y x).

  The first two $a declarations supply only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogLogicEq LogConnectivesNot $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq h x y ) $.
logipedia-connectives-not-syntax $a wff LogConnectivesNot ph $.

${
  $d h x y $.

  logipedia-logic-sym-not-eq $a |-
    A. h
      A. x e. h
        A. y e. h
          (
            LogConnectivesNot ( LogLogicEq h x y )
            ->
            LogConnectivesNot ( LogLogicEq h y x )
          )
  $.
$}
