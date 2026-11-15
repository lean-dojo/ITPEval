$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1144897
  (thousand-theorems__metamath__Q1144897), "Brouwer fixed-point theorem":
  every continuous self-map of a nonempty compact convex subset of an
  arbitrary finite-dimensional real normed vector space has a fixed point.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  V ranges over SetMM normed vector spaces over RRfld, and
  ( dim ` V ) e. NN0 is the finite-dimensionality assumption, including the
  zero-dimensional case. Q1144897Convex expands convexity using V's native
  real scalar multiplication and addition.

  The topology ( TopOpen ` V ) |`t S is the norm topology restricted to S.
  Compactness and continuity are stated for this induced topology, while
  F : S --> S preserves the source's continuous subtype self-map. The fixed
  point remains existentially quantified in the conclusion.

  The final declaration is the single unproved corpus $a statement. The
  preceding $a declarations are syntax and a faithful bidirectional
  definition; this database contains no $p proof statement.
$)

$c Q1144897Convex $.

q1144897-convex-syntax
  $a wff ( Q1144897Convex V S ) $.

${
  $d S V t x y $.

  q1144897-convex-definition $a |- (
    ( Q1144897Convex V S )
    <->
    A. x e. S A. y e. S A. t e. ( 0 [,] 1 )
      (
        (
          ( t ( .s ` V ) x )
          ( +g ` V )
          ( ( 1 - t ) ( .s ` V ) y )
        )
        e. S
      )
  ) $.
$}

${
  $d F S V v x $.

  thousand-theorems-metamath-Q1144897-brouwer-fixed-point $a |-
    A. V e. { v e. NrmVec | ( Scalar ` v ) = RRfld }
      A. S e. ~P ( Base ` V )
        (
          (
            ( dim ` V ) e. NN0
            /\
            (
              S =/= (/)
              /\
              (
                ( Q1144897Convex V S )
                /\
                ( ( TopOpen ` V ) |`t S ) e. Comp
              )
            )
          )
          ->
          A. F
            (
              (
                F : S --> S
                /\
                F e.
                  (
                    ( ( TopOpen ` V ) |`t S )
                    Cn
                    ( ( TopOpen ` V ) |`t S )
                  )
              )
              ->
              E. x e. S ( F ` x ) = x
            )
        )
  $.
$}
