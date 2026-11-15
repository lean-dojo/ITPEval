$(
  Statement-only formalization of PutnamBench artifact putnam_1962_a3:
  the area ratio for the triangle formed by pairwise intersections of three
  cevians whose side points divide a noncollinear real-plane triangle in a
  common positive ratio. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P62A3R2 is the real coordinate plane. P62A3Dist is Euclidean distance,
  P62A3Segment is the closed affine segment, and P62A3Noncol is determinant
  noncollinearity. P62A3Hull is the convex hull of three points via
  nonnegative barycentric coordinates, and P62A3Area is its planar Lebesgue
  measure through the set.mm finite-dimensional volume function voln.

  The final unproved $a assertion universally quantifies the nine points and
  the positive real ratio, and preserves all side-division, intersection,
  and area-ratio conditions from the Lean and Isabelle sources.
$)

$c P62A3I P62A3R2 P62A3Dist P62A3Segment $.
$c P62A3Noncol P62A3Hull P62A3Area $.

p62a3-index-syntax $a class P62A3I $.
p62a3-plane-syntax $a class P62A3R2 $.
p62a3-distance-syntax $a class ( P62A3Dist A B ) $.
p62a3-segment-syntax $a class ( P62A3Segment A B ) $.
p62a3-noncollinear-syntax $a wff ( P62A3Noncol A B C ) $.
p62a3-hull-syntax $a class ( P62A3Hull A B C ) $.
p62a3-area-syntax $a class ( P62A3Area A B C ) $.

p62a3-index-definition $a |- P62A3I = ( 1 ... 2 ) $.

p62a3-plane-definition $a |- P62A3R2 = ( RR ^m P62A3I ) $.

${
  $d A B j $.

  p62a3-distance-definition $a |- (
    P62A3Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P62A3I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B j t z $.

  p62a3-segment-definition $a |- (
    P62A3Segment A B
  ) = {
    z e. P62A3R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P62A3I |->
            (
              ( ( 1 - t ) x. ( A ` j ) )
              +
              ( t x. ( B ` j ) )
            )
        )
  } $.
$}

p62a3-noncollinear-definition $a |- (
  ( P62A3Noncol A B C )
  <->
  (
    (
      ( ( B ` 1 ) - ( A ` 1 ) )
      x.
      ( ( C ` 2 ) - ( A ` 2 ) )
    )
    =/=
    (
      ( ( B ` 2 ) - ( A ` 2 ) )
      x.
      ( ( C ` 1 ) - ( A ` 1 ) )
    )
  )
) $.

${
  $d A B C j u v w x $.

  p62a3-hull-definition $a |- (
    P62A3Hull A B C
  ) = {
    x e. P62A3R2 |
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
              j e. P62A3I |->
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

p62a3-area-definition $a |- (
  P62A3Area A B C
) = (
  ( voln ` P62A3I )
  `
  ( P62A3Hull A B C )
) $.

${
  $d A B C D E F K P Q R $.

  putnambench-putnam-1962-a3 $a |- (
    A. A e. P62A3R2
    A. B e. P62A3R2
    A. C e. P62A3R2
    A. D e. P62A3R2
    A. E e. P62A3R2
    A. F e. P62A3R2
    A. P e. P62A3R2
    A. Q e. P62A3R2
    A. R e. P62A3R2
    A. K e. RR
      (
        (
          0 < K
          /\
          (
            ( P62A3Noncol A B C )
            /\
            (
              (
                D e. ( P62A3Segment B C )
                /\
                ( ( P62A3Dist C D ) / ( P62A3Dist D B ) ) = K
              )
              /\
              (
                (
                  E e. ( P62A3Segment C A )
                  /\
                  ( ( P62A3Dist A E ) / ( P62A3Dist E C ) ) = K
                )
                /\
                (
                  (
                    F e. ( P62A3Segment A B )
                    /\
                    ( ( P62A3Dist B F ) / ( P62A3Dist F A ) ) = K
                  )
                  /\
                  (
                    (
                      P e. ( P62A3Segment B E )
                      /\
                      P e. ( P62A3Segment C F )
                    )
                    /\
                    (
                      (
                        Q e. ( P62A3Segment C F )
                        /\
                        Q e. ( P62A3Segment A D )
                      )
                      /\
                      (
                        R e. ( P62A3Segment A D )
                        /\
                        R e. ( P62A3Segment B E )
                      )
                    )
                  )
                )
              )
            )
          )
        )
        ->
        (
          ( P62A3Area P Q R )
          /
          ( P62A3Area A B C )
        )
        =
        (
          ( ( K - 1 ) ^ 2 )
          /
          ( ( ( K ^ 2 ) + K ) + 1 )
        )
      )
  ) $.
$}
