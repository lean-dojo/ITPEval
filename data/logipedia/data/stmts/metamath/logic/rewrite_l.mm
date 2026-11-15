$(
  Statement-only formalization of the Logipedia corpus artifact logic.rewrite_l
  (logipedia__metamath__logic.rewrite_l), catalog title "logic.rewrite_l":
  left-to-right equality rewriting transports an arbitrary predicate from x
  to an equal element y in an arbitrary type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. The genuine SetMM set variable h represents the arbitrary
  source type A, while p e. ~P h represents an arbitrary predicate on h
  extensionally.
  Membership x e. p and y e. p therefore encode P x and P y, respectively,
  and the restricted quantifiers preserve the source typed binders.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq h x y ) $.

${
  $d h p x y $.

  logipedia-logic-rewrite-l $a |-
    A. h
      A. x e. h
        A. p e. ~P h
          (
            x e. p
            ->
            A. y e. h
              (
                ( LogLogicEq h x y )
                ->
                y e. p
              )
          )
  $.
$}
