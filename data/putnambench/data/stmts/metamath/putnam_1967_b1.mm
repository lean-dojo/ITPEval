$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_b1: a cyclically ordered hexagon inscribed in a circle, with
  three alternating side lengths equal to the radius, has an equilateral
  triangle formed by the midpoints of the other three sides. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P67B1I is the two-coordinate index set, P67B1V is the six-element cyclic
  vertex index set, and P67B1R2 is the real coordinate plane with its
  standard finite product topology P67B1Top. P67B1Succ is cyclic successor
  on 0 ... 5. P67B1Dist is Euclidean distance, P67B1Mid is coordinatewise
  midpoint, P67B1Segment is the closed affine segment, and P67B1Hull is the
  convex hull of the finite vertex range via nonnegative barycentric weights.

  Reindexing ZMod 6 by 0 ... 5 preserves its cyclic successor and all
  quantifiers exactly. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

$c P67B1I P67B1V P67B1R2 P67B1Top P67B1Succ $.
$c P67B1Dist P67B1Mid P67B1Segment P67B1Hull $.

p67b1-coordinate-index-syntax $a class P67B1I $.
p67b1-vertex-index-syntax $a class P67B1V $.
p67b1-plane-syntax $a class P67B1R2 $.
p67b1-topology-syntax $a class P67B1Top $.
p67b1-successor-syntax $a class P67B1Succ $.
p67b1-distance-syntax $a class ( P67B1Dist A B ) $.
p67b1-midpoint-syntax $a class ( P67B1Mid A B ) $.
p67b1-segment-syntax $a class ( P67B1Segment A B ) $.
p67b1-hull-syntax $a class ( P67B1Hull A ) $.

p67b1-coordinate-index-definition $a |- P67B1I = ( 1 ... 2 ) $.

p67b1-vertex-index-definition $a |- P67B1V = ( 0 ... 5 ) $.

p67b1-plane-definition $a |- P67B1R2 = ( RR ^m P67B1I ) $.

p67b1-topology-definition $a |- P67B1Top =
  (
    Xt_ `
      ( P67B1I X. { ( topGen ` ran (,) ) } )
  )
$.

p67b1-successor-definition $a |- P67B1Succ = (
  i e. P67B1V |->
    if (
      i = 5 ,
      0 ,
      ( i + 1 )
    )
) $.

${
  $d A B j $.

  p67b1-distance-definition $a |- (
    P67B1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P67B1I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.

  p67b1-midpoint-definition $a |- (
    P67B1Mid A B
  ) = (
    j e. P67B1I |->
      (
        ( ( A ` j ) + ( B ` j ) )
        /
        2
      )
  ) $.
$}

${
  $d A B j t z $.

  p67b1-segment-definition $a |- (
    P67B1Segment A B
  ) = {
    z e. P67B1R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P67B1I |->
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

  p67b1-hull-definition $a |- (
    P67B1Hull A
  ) = {
    z e. P67B1R2 |
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
              j e. P67B1I |->
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

${
  $d L O P Q R i j r $.

  putnambench-putnam-1967-b1 $a |- (
    A. r e. RR
    A. L e. ( P67B1R2 ^m P67B1V )
    A. P e. P67B1R2
    A. Q e. P67B1R2
    A. R e. P67B1R2
      (
        (
          P = ( P67B1Mid ( L ` 1 ) ( L ` 2 ) )
          /\
          (
            Q = ( P67B1Mid ( L ` 3 ) ( L ` 4 ) )
            /\
            (
              R = ( P67B1Mid ( L ` 5 ) ( L ` 0 ) )
              /\
              (
                0 < r
                /\
                (
                  E. O e. P67B1R2
                    A. i e. P67B1V
                      ( P67B1Dist O ( L ` i ) ) = r
                  /\
                  (
                    A. i e. P67B1V
                    A. j e. P67B1V
                      (
                        i =/= j
                        ->
                        (
                          ( P67B1Succ ` i ) = j
                          \/
                          (
                            i = ( P67B1Succ ` j )
                            \/
                            (
                              (
                                P67B1Segment
                                  ( L ` i )
                                  ( L ` j )
                              )
                              i^i
                              (
                                ( int ` P67B1Top )
                                `
                                ( P67B1Hull ( ran L ) )
                              )
                            )
                            =/=
                            (/)
                          )
                        )
                      )
                    /\
                    (
                      (
                        ( P67B1Dist ( L ` 0 ) ( L ` 1 ) ) = r
                        /\
                        (
                          ( P67B1Dist ( L ` 2 ) ( L ` 3 ) ) = r
                          /\
                          ( P67B1Dist ( L ` 4 ) ( L ` 5 ) ) = r
                        )
                      )
                      /\
                      (
                        ( L ` 1 ) =/= ( L ` 2 )
                        /\
                        (
                          ( L ` 3 ) =/= ( L ` 4 )
                          /\
                          ( L ` 5 ) =/= ( L ` 0 )
                        )
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
          ( P67B1Dist P Q ) = ( P67B1Dist R P )
          /\
          ( P67B1Dist Q R ) = ( P67B1Dist P Q )
        )
      )
  ) $.
$}
