$(
  Statement-only formalization of the Logipedia corpus artifact logic.eq_ind_r
  (logipedia__metamath__logic.eq_ind_r), catalog title "logic.eq_ind_r":
  right-oriented equality induction transports an arbitrary predicate from an
  element a to any x equal to a in an arbitrary type. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. A genuine SetMM set variable h represents the source
  type, while p e. ~P h represents an arbitrary predicate on h extensionally.
  Membership a e. p and x e. p therefore encode P a and P x, respectively,
  and the restricted quantifiers preserve the source typed binders.

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq A B C ) $.

${
  $d a h p x $.

  logipedia-logic-eq-ind-r $a |-
    A. h
      A. a e. h
        A. p e. ~P h
          (
            a e. p
            ->
            A. x e. h
              (
                ( LogLogicEq h x a )
                ->
                x e. p
              )
          )
  $.
$}
