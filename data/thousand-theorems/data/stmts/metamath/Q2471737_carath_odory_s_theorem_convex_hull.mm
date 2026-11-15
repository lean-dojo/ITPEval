$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2471737
  (thousand-theorems__metamath__Q2471737), "Carath&eacute;odory's theorem (convex
  hull)": over an ordered field, the convex hull of an arbitrary subset of a
  module is the union of the convex hulls of its finite affine-independent
  subsets. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q2471737AffineIndependent K V T says that the finite subset T of the module
  V is affine-independent over K: any scalar coefficients on T whose sum and
  weighted vector sum both vanish are all zero.

  Q2471737ConvexHull K V S is the set of all finite convex combinations of
  points of the arbitrary subset S. The finite carrier W, coefficient
  function c, and point function p remain internally existentially quantified.

  The final declaration writes the indexed union extensionally: a point lies
  on the right exactly when it lies in the convex hull of some finite
  affine-independent subset T of S. It is the single unproved corpus $a
  statement. All preceding $a declarations are syntax or faithful
  definitions, and this database contains no $p proof statement.
$)

$c Q2471737AffineIndependent Q2471737ConvexHull $.

q2471737-affine-independent-syntax
  $a wff ( Q2471737AffineIndependent K V T ) $.
q2471737-convex-hull-syntax
  $a class ( Q2471737ConvexHull K V S ) $.

${
  $d K T V c i $.

  q2471737-affine-independent-definition $a |-
    (
      ( Q2471737AffineIndependent K V T )
      <->
      A. c e. ( ( Base ` K ) ^m T )
        (
          (
            (
              K gsum
                ( i e. T |-> ( c ` i ) )
            )
            =
            ( 0g ` K )
            /\
            (
              V gsum
                (
                  i e. T |->
                    (
                      ( c ` i )
                      ( .s ` V )
                      i
                    )
                )
            )
            =
            ( 0g ` V )
          )
          ->
          A. i e. T
            ( c ` i ) = ( 0g ` K )
        )
    )
  $.
$}

${
  $d K S V W c i p x $.

  q2471737-convex-hull-definition $a |-
    ( Q2471737ConvexHull K V S )
    =
    {
      x e. ( Base ` V ) |
        E. W e. Fin
          E. c e. ( ( Base ` K ) ^m W )
            E. p e. ( S ^m W )
              (
                A. i e. W
                  ( 0g ` K ) ( le ` K ) ( c ` i )
                /\
                (
                  (
                    K gsum
                      ( i e. W |-> ( c ` i ) )
                  )
                  =
                  ( 1r ` K )
                  /\
                  x
                  =
                  (
                    V gsum
                      (
                        i e. W |->
                          (
                            ( c ` i )
                            ( .s ` V )
                            ( p ` i )
                          )
                      )
                  )
                )
              )
    }
  $.
$}

${
  $d K S T V x $.

  thousand-theorems-q2471737-caratheodory-convex-hull $a |-
    A. K e. oField
      A. V e. { v e. LMod | ( Scalar ` v ) = K }
        A. S e. ~P ( Base ` V )
          ( Q2471737ConvexHull K V S )
          =
          {
            x e. ( Base ` V ) |
              E. T e. ( ~P S i^i Fin )
                (
                  ( Q2471737AffineIndependent K V T )
                  /\
                  x e. ( Q2471737ConvexHull K V T )
                )
          }
  $.
$}
