$(
  Statement-only formalization of Thousand Theorems corpus artifact Q609612
  (thousand-theorems__metamath__Q609612), "Knaster-Tarski theorem": the fixed
  points of a monotone self-map of an arbitrary complete lattice form a
  complete lattice under the inherited order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q609612FixedPoints(K,F) is the subset of the base of K fixed by F.
  Q609612CompleteSuborder(K,P) states directly that every subset of P has a
  least upper bound and a greatest lower bound in P for the order inherited
  from K. For a subposet of K, this is equivalent to carrying the complete
  lattice structure used by Lean's fixedPoints.completeLattice instance.

  The declarations before the final assertion are syntax or bidirectional
  definitions. The final $a assertion is the single unproved corpus
  statement; this database contains no $p proof statement.
$)

$c Q609612FixedPoints Q609612CompleteSuborder $.

q609612-fixed-points-syntax $a class
  ( Q609612FixedPoints K F ) $.

q609612-complete-suborder-syntax $a wff
  ( Q609612CompleteSuborder K P ) $.

${
  $d F K x $.

  q609612-fixed-points-definition $a |- (
    ( Q609612FixedPoints K F )
    =
    { x e. ( Base ` K ) | ( F ` x ) = x }
  ) $.
$}

${
  $d K P S g u x z $.

  q609612-complete-suborder-definition $a |- (
    ( Q609612CompleteSuborder K P )
    <->
    (
      P C_ ( Base ` K )
      /\
      A. S e. ~P P
        (
          E. u e. P
            (
              A. x e. S x ( le ` K ) u
              /\
              A. z e. P
                (
                  A. x e. S x ( le ` K ) z
                  ->
                  u ( le ` K ) z
                )
            )
          /\
          E. g e. P
            (
              A. x e. S g ( le ` K ) x
              /\
              A. z e. P
                (
                  A. x e. S z ( le ` K ) x
                  ->
                  z ( le ` K ) g
                )
            )
        )
    )
  ) $.
$}

${
  $d F K x y $.

  thousand-theorems-q609612-knaster-tarski-theorem $a |-
    A. K A. F
      (
        (
          (
            K e. CLat
            /\
            F : ( Base ` K ) --> ( Base ` K )
          )
          /\
          A. x e. ( Base ` K )
            A. y e. ( Base ` K )
              (
                x ( le ` K ) y
                ->
                ( F ` x ) ( le ` K ) ( F ` y )
              )
        )
        ->
        ( Q609612CompleteSuborder K
          ( Q609612FixedPoints K F ) )
      )
  $.
$}
