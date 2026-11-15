$(
  Statement-only formalization of "Heron's Formula" from Hundred Theorems
  item 057: the planar Lebesgue area of a triangle equals the square root of
  the product formed from its semiperimeter and three side deficits. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  HT057I is the two-coordinate index set and HT057R2 is the set.mm model of
  the real Euclidean plane. HT057Dist is the ordinary Euclidean distance.
  HT057Hull is exactly the convex hull of three points, expressed through
  nonnegative barycentric coordinates whose sum is one. HT057Semi is the
  semiperimeter using the same ordering of side lengths as the HOL Light
  source.

  The set.mm function voln on HT057I is finite-dimensional Lebesgue volume,
  so its value on HT057Hull is the planar area of the triangle. The final
  declaration is the unproved statement and contains no $p proof.
$)

$c HT057I HT057R2 HT057Dist HT057Hull HT057Semi $.

ht057-index-syntax $a class HT057I $.
ht057-plane-syntax $a class HT057R2 $.
ht057-distance-syntax $a class ( HT057Dist A B ) $.
ht057-hull-syntax $a class ( HT057Hull A B C ) $.
ht057-semiperimeter-syntax $a class ( HT057Semi A B C ) $.

ht057-index-definition $a |- HT057I = ( 1 ... 2 ) $.

ht057-plane-definition $a |- HT057R2 = ( RR ^m HT057I ) $.

${
  $d A B k $.

  ht057-distance-definition $a |- (
    HT057Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. HT057I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C k u v w x $.

  ht057-hull-definition $a |- (
    HT057Hull A B C
  ) = {
    x e. HT057R2 |
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
              k e. HT057I |->
                (
                  (
                    ( u x. ( A ` k ) )
                    +
                    ( v x. ( B ` k ) )
                  )
                  +
                  ( w x. ( C ` k ) )
                )
            )
        )
      )
  } $.
$}

ht057-semiperimeter-definition $a |- (
  HT057Semi A B C
) = (
  (
    (
      ( HT057Dist C B )
      +
      ( HT057Dist A C )
    )
    +
    ( HT057Dist B A )
  )
  /
  2
) $.

${
  $d A B C $.

  hundred-theorems-057-heron $a |- (
    A. A e. HT057R2
    A. B e. HT057R2
    A. C e. HT057R2
      (
        (
          ( voln ` HT057I )
          `
          ( HT057Hull A B C )
        )
        =
        (
          sqrt
          `
          (
            ( HT057Semi A B C )
            x.
            (
              (
                ( HT057Semi A B C )
                -
                ( HT057Dist C B )
              )
              x.
              (
                (
                  ( HT057Semi A B C )
                  -
                  ( HT057Dist A C )
                )
                x.
                (
                  ( HT057Semi A B C )
                  -
                  ( HT057Dist B A )
                )
              )
            )
          )
        )
      )
  ) $.
$}
