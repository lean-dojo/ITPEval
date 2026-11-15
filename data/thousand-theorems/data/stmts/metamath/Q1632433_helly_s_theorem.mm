$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1632433
  (thousand-theorems__metamath__Q1632433), "Helly's theorem": a finite family
  of convex subsets of a finite-dimensional vector space over an ordered field
  has nonempty total intersection when it has at least dimension plus one
  members and every subfamily of exactly that size has nonempty intersection.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K and V range over the same ordered fields and modules as the Lean source.
  The condition ( dim ` V ) e. NN0 expresses finite dimensionality. A is an
  arbitrary index set, S is the source finset of selected indices, and F maps
  every index to an arbitrary subset of V's carrier.

  Q1632433Convex is the ordered-field definition of convexity: every
  nonnegative two-coefficient affine combination whose coefficients sum to
  one remains in the set. Q1632433Intersects keeps the common point
  existentially quantified and states membership in every set indexed by the
  given subfamily. Thus both the source's subfamily I and every intersection
  witness remain internal to the statement.

  Among the declarations authored in this root artifact, those before the
  final one are syntax or bidirectional definitions. The final $a declaration
  is the single unproved corpus statement. This root artifact contains no $p
  proof statement; imported lib/set.mm supplies the library proofs verified
  by ITPEval.
$)

$c Q1632433Convex Q1632433Intersects $.

q1632433-convex-syntax
  $a wff ( Q1632433Convex K V T ) $.
q1632433-intersects-syntax
  $a wff ( Q1632433Intersects V F I ) $.

${
  $d K T V a b x y $.

  q1632433-convex-definition $a |- (
    ( Q1632433Convex K V T )
    <->
    (
      T C_ ( Base ` V )
      /\
      A. x e. T
        A. y e. T
          A. a e. ( Base ` K )
            A. b e. ( Base ` K )
              (
                (
                  (
                    ( 0g ` K ) ( le ` K ) a
                    /\
                    ( 0g ` K ) ( le ` K ) b
                  )
                  /\
                  ( a ( +g ` K ) b ) = ( 1r ` K )
                )
                ->
                (
                  (
                    a ( .s ` V ) x
                  )
                  ( +g ` V )
                  (
                    b ( .s ` V ) y
                  )
                )
                e. T
              )
    )
  ) $.
$}

${
  $d F I V i x $.

  q1632433-intersects-definition $a |- (
    ( Q1632433Intersects V F I )
    <->
    E. x e. ( Base ` V )
      A. i e. I
        x e. ( F ` i )
  ) $.
$}

${
  $d A F I K S V i $.

  thousand-theorems-q1632433-helly $a |- (
    A. K e. oField
      A. V e. { v e. LMod | ( Scalar ` v ) = K }
        A. A
          A. F e. ( ( ~P ( Base ` V ) ) ^m A )
            A. S e. ( ~P A i^i Fin )
              (
                (
                  (
                    ( dim ` V ) e. NN0
                    /\
                    (
                      ( ( dim ` V ) + 1 )
                      <_
                      ( # ` S )
                    )
                  )
                  /\
                  A. i e. S
                    ( Q1632433Convex K V ( F ` i ) )
                )
                /\
                A. I e. ( ~P S i^i Fin )
                  (
                    (
                      ( # ` I )
                      =
                      ( ( dim ` V ) + 1 )
                    )
                    ->
                    ( Q1632433Intersects V F I )
                  )
              )
              ->
              ( Q1632433Intersects V F S )
  ) $.
$}
