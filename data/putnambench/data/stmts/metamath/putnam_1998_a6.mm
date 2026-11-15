$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_a6: distinct integer-coordinate points in the real plane
  satisfying the stated distance and triangle-area inequality are three
  vertices of a square. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P98A6I is the two-coordinate index set and P98A6R2 is the real plane.
  P98A6Dist is Euclidean distance. P98A6Hull is the convex hull of three
  points via nonnegative barycentric coordinates, and P98A6Area is its
  planar Lebesgue measure through set.mm's finite-dimensional volume.
  P98A6ThreeSquare P Q R states that the rays from Q to P and R have equal
  length and zero inner product, so P, Q, and R are three consecutive
  vertices of a square.

  Quantification over ZZ-valued functions on P98A6I is equivalent to the
  real-plane point type together with the integer-coordinate hypothesis in
  the Lean and Isabelle sources. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

$c P98A6I P98A6R2 P98A6Dist P98A6Hull P98A6Area P98A6Dot
   P98A6ThreeSquare $.

p98a6-index-syntax $a class P98A6I $.
p98a6-plane-syntax $a class P98A6R2 $.
p98a6-distance-syntax $a class ( P98A6Dist A B ) $.
p98a6-hull-syntax $a class ( P98A6Hull A B C ) $.
p98a6-area-syntax $a class ( P98A6Area A B C ) $.
p98a6-dot-syntax $a class ( P98A6Dot A B C ) $.
p98a6-three-square-syntax $a wff ( P98A6ThreeSquare A B C ) $.

p98a6-index-definition $a |- P98A6I = ( 1 ... 2 ) $.

p98a6-plane-definition $a |- P98A6R2 = ( RR ^m P98A6I ) $.

${
  $d A B j $.

  p98a6-distance-definition $a |- (
    P98A6Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P98A6I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C j u v w x $.

  p98a6-hull-definition $a |- (
    P98A6Hull A B C
  ) = {
    x e. P98A6R2 |
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
              j e. P98A6I |->
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

p98a6-area-definition $a |- (
  P98A6Area A B C
) = (
  ( voln ` P98A6I )
  `
  ( P98A6Hull A B C )
) $.

${
  $d A B C j $.

  p98a6-dot-definition $a |- (
    P98A6Dot A B C
  ) = (
    sum_ j e. P98A6I
      (
        ( ( A ` j ) - ( B ` j ) )
        x.
        ( ( C ` j ) - ( B ` j ) )
      )
  ) $.
$}

p98a6-three-square-definition $a |- (
  ( P98A6ThreeSquare A B C )
  <->
  (
    ( P98A6Dist B A ) = ( P98A6Dist B C )
    /\
    ( P98A6Dot A B C ) = 0
  )
) $.

${
  $d a b c $.

  putnambench-putnam-1998-a6 $a |-
    A. a e. ( ZZ ^m P98A6I )
    A. b e. ( ZZ ^m P98A6I )
    A. c e. ( ZZ ^m P98A6I )
      (
        (
          (
            a =/= b
            /\
            (
              a =/= c
              /\
              b =/= c
            )
          )
          /\
          (
            ( ( P98A6Dist a b ) + ( P98A6Dist b c ) ) ^ 2
            <
            ( ( 8 x. ( P98A6Area a b c ) ) + 1 )
          )
        )
        ->
        (
          ( P98A6ThreeSquare a b c )
          \/
          (
            ( P98A6ThreeSquare b c a )
            \/
            ( P98A6ThreeSquare c a b )
          )
        )
      )
  $.
$}
