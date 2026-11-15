$(
  Statement-only formalization of the Logipedia corpus artifact
  logic.eq_rect_r (logipedia__metamath__logic.eq_rect_r), catalog title
  "logic.eq_rect_r": right-oriented equality elimination transports an
  arbitrary predicate from a to x when x is equal to a in an arbitrary type.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. A genuine SetMM set variable h represents the source
  type, while p e. ~P h represents an arbitrary predicate on h extensionally.
  Membership a e. p and x e. p therefore encode P a and P x, respectively.
  The binder order preserves the source declaration: A, a, x, the equality
  premise, then P and its implication from P a to P x.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq A B C ) $.

${
  $d a h p x $.

  logipedia-logic-eq-rect-r $a |-
    A. h
      A. a e. h
        A. x e. h
          (
            ( LogLogicEq h x a )
            ->
            A. p e. ~P h
              (
                a e. p
                ->
                x e. p
              )
          )
  $.
$}
