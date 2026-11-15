$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_a1: two area inequalities for side points of a noncollinear
  triangle in the real Euclidean plane. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P73A1R2 is the real coordinate plane. P73A1Dist is Euclidean distance,
  P73A1Segment is the closed affine segment, and P73A1Noncol is determinant
  noncollinearity. P73A1Hull is the convex hull of three points via
  nonnegative barycentric coordinates, and P73A1Area is its planar Lebesgue
  measure through the set.mm finite-dimensional volume function voln.

  The final unproved $a assertion universally quantifies the six points. Its
  second area conclusion writes the infimum inequality for a nonempty
  three-element set equivalently as a disjunction that one of its members is
  at most the area of the central triangle. This database contains no $p
  proof statement.
$)

$c P73A1I P73A1R2 P73A1Dist P73A1Segment $.
$c P73A1Noncol P73A1Hull P73A1Area $.

p73a1-index-syntax $a class P73A1I $.
p73a1-plane-syntax $a class P73A1R2 $.
p73a1-distance-syntax $a class ( P73A1Dist A B ) $.
p73a1-segment-syntax $a class ( P73A1Segment A B ) $.
p73a1-noncollinear-syntax $a wff ( P73A1Noncol A B C ) $.
p73a1-hull-syntax $a class ( P73A1Hull A B C ) $.
p73a1-area-syntax $a class ( P73A1Area A B C ) $.

p73a1-index-definition $a |- P73A1I = ( 1 ... 2 ) $.

p73a1-plane-definition $a |- P73A1R2 = ( RR ^m P73A1I ) $.

${
  $d A B j $.

  p73a1-distance-definition $a |- (
    P73A1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P73A1I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B j t z $.

  p73a1-segment-definition $a |- (
    P73A1Segment A B
  ) = {
    z e. P73A1R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P73A1I |->
            (
              ( ( 1 - t ) x. ( A ` j ) )
              +
              ( t x. ( B ` j ) )
            )
        )
  } $.
$}

p73a1-noncollinear-definition $a |- (
  ( P73A1Noncol A B C )
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

  p73a1-hull-definition $a |- (
    P73A1Hull A B C
  ) = {
    x e. P73A1R2 |
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
              j e. P73A1I |->
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

p73a1-area-definition $a |- (
  P73A1Area A B C
) = (
  ( voln ` P73A1I )
  `
  ( P73A1Hull A B C )
) $.

${
  $d A B C X Y Z $.

  putnambench-putnam-1973-a1 $a |- (
    A. A e. P73A1R2
    A. B e. P73A1R2
    A. C e. P73A1R2
    A. X e. P73A1R2
    A. Y e. P73A1R2
    A. Z e. P73A1R2
      (
        (
          ( P73A1Noncol A B C )
          /\
          (
            X e. ( P73A1Segment B C )
            /\
            (
              Y e. ( P73A1Segment C A )
              /\
              Z e. ( P73A1Segment A B )
            )
          )
        )
        ->
        (
          (
            (
              ( P73A1Dist B X ) <_ ( P73A1Dist X C )
              /\
              (
                ( P73A1Dist C Y ) <_ ( P73A1Dist Y A )
                /\
                ( P73A1Dist A Z ) <_ ( P73A1Dist Z B )
              )
            )
            ->
            (
              ( ( 1 / 4 ) x. ( P73A1Area A B C ) )
              <_
              ( P73A1Area X Y Z )
            )
          )
          /\
          (
            ( P73A1Area A Z Y ) <_ ( P73A1Area X Y Z )
            \/
            (
              ( P73A1Area B X Z ) <_ ( P73A1Area X Y Z )
              \/
              ( P73A1Area C Y X ) <_ ( P73A1Area X Y Z )
            )
          )
        )
      )
  ) $.
$}
