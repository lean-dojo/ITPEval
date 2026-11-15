$(
  Statement-only formalization of the Logipedia corpus artifact logic.eq_f2
  (logipedia__metamath__logic.eq_f2), catalog title "logic.eq_f2": a curried
  binary function between arbitrary types preserves the module's polymorphic
  equality in both arguments. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEq represents the source module's opaque type-indexed equality
  predicate logic.eq. Genuine SetMM set variables h, i, and j represent the
  source types A, B, and C; ( ( j ^m i ) ^m h ) is the class of all curried
  total functions A -> B -> C. The restricted variables x, y in h encode
  x1, x2, and z, w in i encode y1, y2. Thus the final implication is exactly
  logic.eq A x1 x2 -> logic.eq B y1 y2 ->
  logic.eq C (f x1 y1) (f x2 y2).

  The first $a declaration supplies only predicate syntax. The final $a
  declaration is Metamath's native unproved statement encoding; this database
  contains no $p proof declaration.
$)

$c LogLogicEq $.

logipedia-logic-eq-syntax $a wff ( LogLogicEq A B C ) $.

${
  $d f h i j w x y z $.

  logipedia-logic-eq-f2 $a |-
    A. h A. i A. j
      A. f e. ( ( j ^m i ) ^m h )
        A. x e. h
          A. y e. h
            A. z e. i
              A. w e. i
                (
                  ( LogLogicEq h x y )
                  ->
                  (
                    ( LogLogicEq i z w )
                    ->
                    (
                      LogLogicEq
                      j
                      ( ( f ` x ) ` z )
                      ( ( f ` y ) ` w )
                    )
                  )
                )
  $.
$}
