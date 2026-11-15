$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_b6: a nondegenerate ordered quadrilateral circumscribed about
  a circle, whose area is the square root of the product of its four side
  lengths, is cyclic. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P70B6I and P70B6V are the two-coordinate and four-vertex index sets.
  P70B6R2 is the real Euclidean plane with its standard finite product
  topology P70B6Top, and P70B6Succ is cyclic successor on 0 ... 3.
  P70B6Dist, P70B6Segment, P70B6Hull, and P70B6Col expand Euclidean
  distance, closed affine segments, finite convex hulls, and determinant
  collinearity. P70B6NoncolSet expresses noncollinearity of every three
  distinct points in a set. P70B6UniqueTangency is existence and uniqueness
  in the plane of a point on a specified line at a specified distance from
  the center.

  Reindexing ZMod 4 by 0 ... 3 preserves cyclic successor. The final
  unproved $a assertion preserves the arbitrary vertex map and set, the
  four-point and noncollinearity conditions, positive side lengths, boundary
  ordering, internally existential incircle center and radius with unique
  tangencies, planar Lebesgue-area equality, and internally existential
  circumcircle. This database contains no $p proof statement.
$)

$c P70B6I P70B6V P70B6R2 P70B6Top P70B6Succ $.
$c P70B6Dist P70B6Segment P70B6Hull P70B6Col $.
$c P70B6NoncolSet P70B6UniqueTangency $.

p70b6-coordinate-index-syntax $a class P70B6I $.
p70b6-vertex-index-syntax $a class P70B6V $.
p70b6-plane-syntax $a class P70B6R2 $.
p70b6-topology-syntax $a class P70B6Top $.
p70b6-successor-syntax $a class P70B6Succ $.
p70b6-distance-syntax $a class ( P70B6Dist A B ) $.
p70b6-segment-syntax $a class ( P70B6Segment A B ) $.
p70b6-hull-syntax $a class ( P70B6Hull A ) $.
p70b6-collinear-syntax $a wff ( P70B6Col A B C ) $.
p70b6-noncollinear-set-syntax $a wff ( P70B6NoncolSet A ) $.
p70b6-unique-tangency-syntax $a
  wff ( P70B6UniqueTangency O r A B ) $.

p70b6-coordinate-index-definition $a |- P70B6I = ( 1 ... 2 ) $.

p70b6-vertex-index-definition $a |- P70B6V = ( 0 ... 3 ) $.

p70b6-plane-definition $a |- P70B6R2 = ( RR ^m P70B6I ) $.

p70b6-topology-definition $a |- P70B6Top =
  (
    Xt_ `
      ( P70B6I X. { ( topGen ` ran (,) ) } )
  )
$.

p70b6-successor-definition $a |- P70B6Succ = (
  i e. P70B6V |->
    if (
      i = 3 ,
      0 ,
      ( i + 1 )
    )
) $.

${
  $d A B j $.

  p70b6-distance-definition $a |- (
    P70B6Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P70B6I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B j t z $.

  p70b6-segment-definition $a |- (
    P70B6Segment A B
  ) = {
    z e. P70B6R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P70B6I |->
            (
              ( ( 1 - t ) x. ( A ` j ) )
              +
              ( t x. ( B ` j ) )
            )
        )
  } $.
$}

${
  $d A j w x z $.

  p70b6-hull-definition $a |- (
    P70B6Hull A
  ) = {
    z e. P70B6R2 |
    E. w
      (
        (
          w : A --> RR
          /\
          A. x e. A 0 <_ ( w ` x )
        )
        /\
        (
          ( sum_ x e. A ( w ` x ) ) = 1
          /\
          z =
            (
              j e. P70B6I |->
                sum_ x e. A
                  (
                    ( w ` x )
                    x.
                    ( x ` j )
                  )
            )
        )
      )
  } $.
$}

p70b6-collinear-definition $a |- (
  ( P70B6Col A B C )
  <->
  (
    (
      ( ( B ` 1 ) - ( A ` 1 ) )
      x.
      ( ( C ` 2 ) - ( A ` 2 ) )
    )
    =
    (
      ( ( B ` 2 ) - ( A ` 2 ) )
      x.
      ( ( C ` 1 ) - ( A ` 1 ) )
    )
  )
) $.

${
  $d A B C D $.

  p70b6-noncollinear-set-definition $a |- (
    ( P70B6NoncolSet A )
    <->
    (
      A C_ P70B6R2
      /\
      A. B e. A A. C e. A A. D e. A
        (
          (
            B =/= C
            /\
            (
              B =/= D
              /\
              C =/= D
            )
          )
          ->
          -. ( P70B6Col B C D )
        )
    )
  ) $.
$}

${
  $d A B O P Q r $.

  p70b6-unique-tangency-definition $a |- (
    ( P70B6UniqueTangency O r A B )
    <->
    E. P e. P70B6R2
      (
        (
          ( P70B6Col P A B )
          /\
          ( P70B6Dist O P ) = r
        )
        /\
        A. Q e. P70B6R2
          (
            (
              ( P70B6Col Q A B )
              /\
              ( P70B6Dist O Q ) = r
            )
            ->
            Q = P
          )
      )
  ) $.
$}

${
  $d L O P S i r s $.

  putnambench-putnam-1970-b6 $a |-
    A. L e. ( P70B6R2 ^m P70B6V )
    A. S
      (
        (
          S = ran L
          /\
          (
            (
              ( # ` S ) = 4
              /\
              A. s e. { s e. ~P S | ( # ` s ) = 3 }
                ( P70B6NoncolSet s )
            )
            /\
            (
              (
                0 < ( P70B6Dist ( L ` 0 ) ( L ` 1 ) )
                /\
                (
                  0 < ( P70B6Dist ( L ` 1 ) ( L ` 2 ) )
                  /\
                  (
                    0 < ( P70B6Dist ( L ` 2 ) ( L ` 3 ) )
                    /\
                    0 < ( P70B6Dist ( L ` 3 ) ( L ` 0 ) )
                  )
                )
              )
              /\
              (
                A. i e. P70B6V
                  (
                    (
                      P70B6Segment
                        ( L ` i )
                        ( L ` ( P70B6Succ ` i ) )
                    )
                    i^i
                    (
                      ( int ` P70B6Top )
                      `
                      ( P70B6Hull S )
                    )
                  )
                  =
                  (/)
                /\
                (
                  E. O e. P70B6R2 E. r e. RR
                    (
                      O e. ( P70B6Hull S )
                      /\
                      (
                        0 < r
                        /\
                        A. i e. P70B6V
                          (
                            P70B6UniqueTangency
                              O
                              r
                              ( L ` i )
                              ( L ` ( P70B6Succ ` i ) )
                          )
                      )
                    )
                  /\
                  (
                    (
                      ( voln ` P70B6I )
                      `
                      ( P70B6Hull S )
                    )
                    =
                    (
                      sqrt
                      `
                      (
                        (
                          (
                            ( P70B6Dist ( L ` 0 ) ( L ` 1 ) )
                            x.
                            ( P70B6Dist ( L ` 1 ) ( L ` 2 ) )
                          )
                          x.
                          ( P70B6Dist ( L ` 2 ) ( L ` 3 ) )
                        )
                        x.
                        ( P70B6Dist ( L ` 3 ) ( L ` 0 ) )
                      )
                    )
                  )
                )
              )
            )
          )
        )
        ->
        E. O e. P70B6R2 E. r e. RR
          A. P e. S
            ( P70B6Dist P O ) = r
      )
  $.
$}
