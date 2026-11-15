$(
  Statement-only formalization of PutnamBench artifact putnam_1966_b1:
  a convex polygon contained in the unit square has sum of squared side
  lengths at most four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P66B1R2 is the real coordinate plane with its standard finite product
  topology. P66B1Succ is cyclic successor on the reindexed n-element carrier
  1 ... n. P66B1Dist is Euclidean distance, P66B1Segment is the closed affine
  segment, P66B1Noncol is determinant noncollinearity, and P66B1Hull is the
  convex hull of the finite vertex range via nonnegative barycentric weights.

  The pairwise-distinct guard and cyclic final edge follow the Lean statement
  and the mathematical problem description. Their omission from the Isabelle
  noncollinearity premise and final summand is a typographical inconsistency.
  Reindexing ZMod n by 1 ... n preserves the finite cyclic polygon exactly
  under the assumption n >= 3.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P66B1I P66B1R2 P66B1Top P66B1Succ $.
$c P66B1Dist P66B1Segment P66B1Noncol P66B1Hull $.

p66b1-index-syntax $a class P66B1I $.
p66b1-plane-syntax $a class P66B1R2 $.
p66b1-topology-syntax $a class P66B1Top $.
p66b1-successor-syntax $a class ( P66B1Succ N ) $.
p66b1-distance-syntax $a class ( P66B1Dist A B ) $.
p66b1-segment-syntax $a class ( P66B1Segment A B ) $.
p66b1-noncollinear-syntax $a wff ( P66B1Noncol A B C ) $.
p66b1-hull-syntax $a class ( P66B1Hull A ) $.

p66b1-index-definition $a |- P66B1I = ( 1 ... 2 ) $.

p66b1-plane-definition $a |- P66B1R2 = ( RR ^m P66B1I ) $.

p66b1-topology-definition $a |- P66B1Top =
  (
    Xt_ `
      ( P66B1I X. { ( topGen ` ran (,) ) } )
  )
$.

${
  $d N i $.

  p66b1-successor-definition $a |- (
    P66B1Succ N
  ) = (
    i e. ( 1 ... N ) |->
      if (
        i = N ,
        1 ,
        ( i + 1 )
      )
  ) $.
$}

${
  $d A B j $.

  p66b1-distance-definition $a |- (
    P66B1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P66B1I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B j t z $.

  p66b1-segment-definition $a |- (
    P66B1Segment A B
  ) = {
    z e. P66B1R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P66B1I |->
            (
              ( ( 1 - t ) x. ( A ` j ) )
              +
              ( t x. ( B ` j ) )
            )
        )
  } $.
$}

p66b1-noncollinear-definition $a |- (
  ( P66B1Noncol A B C )
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
  $d A j w x z $.

  p66b1-hull-definition $a |- (
    P66B1Hull A
  ) = {
    z e. P66B1R2 |
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
              j e. P66B1I |->
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
  $d L i j k n $.

  putnambench-putnam-1966-b1 $a |-
    A. n e. NN0
    A. L e. ( P66B1R2 ^m ( 1 ... n ) )
      (
        (
          3 <_ n
          /\
          (
            A. i e. ( 1 ... n )
              (
                ( ( L ` i ) ` 1 ) e. ( 0 [,] 1 )
                /\
                ( ( L ` i ) ` 2 ) e. ( 0 [,] 1 )
              )
            /\
            (
              A. i e. ( 1 ... n )
              A. j e. ( 1 ... n )
              A. k e. ( 1 ... n )
                (
                  (
                    i =/= j
                    /\
                    (
                      j =/= k
                      /\
                      k =/= i
                    )
                  )
                  ->
                  ( P66B1Noncol ( L ` i ) ( L ` j ) ( L ` k ) )
                )
              /\
              A. i e. ( 1 ... n )
                (
                  (
                    P66B1Segment
                      ( L ` i )
                      ( L ` ( ( P66B1Succ n ) ` i ) )
                  )
                  i^i
                  (
                    ( int ` P66B1Top )
                    `
                    ( P66B1Hull ( ran L ) )
                  )
                )
                =
                (/)
            )
          )
        )
        ->
        (
          sum_ i e. ( 1 ... n )
            (
              (
                P66B1Dist
                  ( L ` i )
                  ( L ` ( ( P66B1Succ n ) ` i ) )
              )
              ^ 2
            )
        )
        <_
        4
      )
  $.
$}
