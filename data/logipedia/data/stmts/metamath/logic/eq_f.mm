$(
  Statement-only formalization of the Logipedia corpus artifact logic.eq_f
  (logipedia__metamath__logic.eq_f), catalog title "logic.eq_f": an arbitrary
  function between arbitrary types preserves the module's polymorphic
  equality. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. Genuine SetMM set variables h and i represent the source
  types A and B; i ^m h is the class of all total functions from h to i, and
  restricted quantifiers over h preserve the typed binders for x and y. Thus
  the final implication is exactly logic.eq A x y ->
  logic.eq B (f x) (f y).

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq A B C ) $.

${
  $d f h i x y $.

  logipedia-logic-eq-f $a |-
    A. h A. i
      A. f e. ( i ^m h )
        A. x e. h
          A. y e. h
            (
              ( LogLogicEq h x y )
              ->
              ( LogLogicEq i ( f ` x ) ( f ` y ) )
            )
  $.
$}
