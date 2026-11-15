$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1471282
  (thousand-theorems__metamath__Q1471282), "Radon's theorem": every affine
  dependent family in a module over an ordered field admits a subset whose
  image and complementary image have convex hulls with a common point. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1471282AffineIndependent K V A F uses the finite-relation
  characterization of affine independence: every scalar relation on a finite
  subset of the arbitrary index set A whose coefficients and weighted vectors
  both sum to zero has all coefficients zero.

  Q1471282ConvexHull K V S is the set of all finite convex combinations of
  points of S. The finite carrier W, coefficient function c, and point
  function p remain internally existentially quantified. Over an ordered
  field this is equivalent to the source convexHull.

  The final declaration is the single unproved corpus $a statement. Its
  subset I and common point x remain existentially quantified, the complement
  is relative to the full arbitrary index set A, and this database contains no
  $p proof statement.
$)

$c Q1471282AffineIndependent Q1471282ConvexHull $.

q1471282-affine-independent-syntax
  $a wff ( Q1471282AffineIndependent K V A F ) $.
q1471282-convex-hull-syntax
  $a class ( Q1471282ConvexHull K V S ) $.

${
  $d A F K V c i s $.

  q1471282-affine-independent-definition $a |- (
    ( Q1471282AffineIndependent K V A F )
    <->
    A. s e. ( ~P A i^i Fin )
      A. c e. ( ( Base ` K ) ^m s )
        (
          (
            (
              K gsum
                ( i e. s |-> ( c ` i ) )
            )
            =
            ( 0g ` K )
            /\
            (
              V gsum
                (
                  i e. s |->
                    (
                      ( c ` i )
                      ( .s ` V )
                      ( F ` i )
                    )
                )
            )
            =
            ( 0g ` V )
          )
          ->
          A. i e. s
            ( c ` i ) = ( 0g ` K )
        )
  ) $.
$}

${
  $d K S V c i p w x $.

  q1471282-convex-hull-definition $a |-
    ( Q1471282ConvexHull K V S )
    =
    {
      x e. ( Base ` V ) |
        E. w e. Fin
          E. c e. ( ( Base ` K ) ^m w )
            E. p e. ( S ^m w )
              (
                A. i e. w
                  ( 0g ` K ) ( le ` K ) ( c ` i )
                /\
                (
                  (
                    K gsum
                      ( i e. w |-> ( c ` i ) )
                  )
                  =
                  ( 1r ` K )
                  /\
                  x
                  =
                  (
                    V gsum
                      (
                        i e. w |->
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
  $d a f i k v w x $.

  thousand-theorems-q1471282-radon-partition $a |-
    A. k e. oField
      A. w e. { v e. LMod | ( Scalar ` v ) = k }
        A. a
          A. f e. ( ( Base ` w ) ^m a )
            (
              -.
              ( Q1471282AffineIndependent k w a f )
              ->
              E. i e. ~P a
                E. x e. ( Base ` w )
                  (
                    x e.
                      (
                        Q1471282ConvexHull
                        k
                        w
                        ( f " i )
                      )
                    /\
                    x e.
                      (
                        Q1471282ConvexHull
                        k
                        w
                        ( f " ( a \ i ) )
                      )
                  )
            )
  $.
$}
