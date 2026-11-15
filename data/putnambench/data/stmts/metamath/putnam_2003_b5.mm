$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_b5: distances from an interior point to the vertices of a
  nondegenerate equilateral triangle on the unit circle are side lengths of
  a triangle whose area depends only on the point's distance from the center.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P03B5R2 is the real Euclidean plane, P03B5Zero is its origin, and
  P03B5Dist is ordinary Euclidean distance. P03B5Hull is exactly the convex
  hull of three points through nonnegative barycentric coordinates, and
  P03B5Area is its two-dimensional Lebesgue measure via set.mm's voln.

  The final assertion universally quantifies A, B, and C, retains their
  unit-circle, equal-distance, and nondegeneracy assumptions, and internally
  quantifies the total real function f. For every point P in the open unit
  disk, X, Y, and Z remain existentially quantified and realize the three
  prescribed side lengths, with area equal to f at the radial distance of P.
  Every declaration below is an unproved $a statement; there is no $p proof.
$)

$c P03B5I P03B5R2 P03B5Zero P03B5Dist P03B5Hull P03B5Area $.

p03b5-index-syntax $a class P03B5I $.
p03b5-plane-syntax $a class P03B5R2 $.
p03b5-zero-syntax $a class P03B5Zero $.
p03b5-distance-syntax $a class ( P03B5Dist A B ) $.
p03b5-hull-syntax $a class ( P03B5Hull A B C ) $.
p03b5-area-syntax $a class ( P03B5Area A B C ) $.

p03b5-index-definition $a |- P03B5I = ( 1 ... 2 ) $.

p03b5-plane-definition $a |- P03B5R2 = ( RR ^m P03B5I ) $.

p03b5-zero-definition $a |- P03B5Zero =
  ( j e. P03B5I |-> 0 )
$.

${
  $d A B j $.

  p03b5-distance-definition $a |- (
    P03B5Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P03B5I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C j u v w x $.

  p03b5-hull-definition $a |- (
    P03B5Hull A B C
  ) = {
    x e. P03B5R2 |
    E. u e. RR E. v e. RR E. w e. RR
      (
        (
          0 <_ u
          /\
          (
            0 <_ v
            /\
            0 <_ w
          )
        )
        /\
        (
          ( ( u + v ) + w ) = 1
          /\
          x =
            (
              j e. P03B5I |->
                (
                  (
                    ( u x. ( A ` j ) )
                    +
                    ( v x. ( B ` j ) )
                  )
                  +
                  ( w x. ( C ` j ) )
                )
            )
        )
      )
  } $.
$}

p03b5-area-definition $a |- (
  P03B5Area A B C
) = (
  ( voln ` P03B5I )
  `
  ( P03B5Hull A B C )
) $.

${
  $d A B C P X Y Z f $.

  putnambench-putnam-2003-b5 $a |- (
    A. A e. P03B5R2
    A. B e. P03B5R2
    A. C e. P03B5R2
      (
        (
          (
            ( P03B5Dist P03B5Zero A ) = 1
            /\
            (
              ( P03B5Dist P03B5Zero B ) = 1
              /\
              ( P03B5Dist P03B5Zero C ) = 1
            )
          )
          /\
          (
            ( P03B5Dist A B ) = ( P03B5Dist A C )
            /\
            (
              ( P03B5Dist A B ) = ( P03B5Dist B C )
              /\
              ( P03B5Dist A B ) =/= 0
            )
          )
        )
        ->
        E. f e. ( RR ^m RR )
          A. P e. P03B5R2
            (
              ( P03B5Dist P03B5Zero P ) < 1
              ->
              E. X e. P03B5R2
              E. Y e. P03B5R2
              E. Z e. P03B5R2
                (
                  ( P03B5Dist X Y ) = ( P03B5Dist P A )
                  /\
                  (
                    ( P03B5Dist Y Z ) = ( P03B5Dist P B )
                    /\
                    (
                      ( P03B5Dist X Z ) = ( P03B5Dist P C )
                      /\
                      ( P03B5Area X Y Z )
                      =
                      ( f ` ( P03B5Dist P03B5Zero P ) )
                    )
                  )
                )
            )
      )
  ) $.
$}
