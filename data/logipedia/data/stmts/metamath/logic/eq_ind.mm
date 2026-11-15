$(
  Statement-only formalization of the Logipedia corpus artifact logic.eq_ind
  (logipedia__metamath__logic.eq_ind), catalog title "logic.eq_ind": equality
  induction transports an arbitrary predicate between equal elements of an
  arbitrary type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. A genuine SetMM set variable h represents the source
  type, while p e. ~P h represents an arbitrary predicate on h extensionally.
  Membership x e. p and y e. p therefore encode P x and P y, respectively,
  and the restricted quantifiers preserve the source typed binders.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq A B C ) $.

${
  $d h p x y $.

  logipedia-logic-eq-ind $a |-
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
