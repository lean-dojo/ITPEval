$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_b4: every continuous real-plane curve on the closed unit
  interval with extended variation one is covered by a four-vertex rectangle
  whose area is one quarter. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P69B4R2 is the real coordinate plane with its standard finite-product
  topology. P69B4Dist is Euclidean distance, and P69B4Angle A B C is the
  total unoriented angle at B, with value pi/2 when either ray is zero, as in
  Lean's EuclideanGeometry angle.

  P69B4Continuous says that the restriction of the total curve G to [0,1] is
  continuous. P69B4Variation is the supremum of all polygonal sums over
  strictly increasing finite partitions from 0 to 1. This equals the
  extended metric variation on [0,1] when finite; hence equality to one is
  equivalent to the source hypothesis eVariationOn G [0,1] = 1.

  P69B4Hull is the convex hull of a finite point set, expressed through
  internally existential nonnegative barycentric weights. The four rectangle
  vertices in the final assertion are likewise internally existential. The
  final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P69B4I P69B4R2 P69B4Top P69B4Dist P69B4Dot P69B4Angle $.
$c P69B4Hull P69B4Continuous P69B4Variation $.

p69b4-coordinate-index-syntax $a class P69B4I $.
p69b4-plane-syntax $a class P69B4R2 $.
p69b4-topology-syntax $a class P69B4Top $.
p69b4-distance-syntax $a class ( P69B4Dist A B ) $.
p69b4-dot-syntax $a class ( P69B4Dot A B C ) $.
p69b4-angle-syntax $a class ( P69B4Angle A B C ) $.
p69b4-hull-syntax $a class ( P69B4Hull S ) $.
p69b4-continuous-syntax $a wff ( P69B4Continuous G ) $.
p69b4-variation-syntax $a class ( P69B4Variation G ) $.

p69b4-coordinate-index-definition $a |- P69B4I = ( 1 ... 2 ) $.

p69b4-plane-definition $a |- P69B4R2 = ( RR ^m P69B4I ) $.

p69b4-topology-definition $a |- P69B4Top = (
  Xt_ `
    ( P69B4I X. { ( topGen ` ran (,) ) } )
) $.

${
  $d A B k $.

  p69b4-distance-definition $a |- (
    P69B4Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P69B4I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C k $.

  p69b4-dot-definition $a |- (
    P69B4Dot A B C
  ) = (
    sum_ k e. P69B4I
      (
        ( ( A ` k ) - ( B ` k ) )
        x.
        ( ( C ` k ) - ( B ` k ) )
      )
  ) $.
$}

p69b4-angle-definition $a |- (
  P69B4Angle A B C
) = if (
  (
    ( ( P69B4Dist A B ) = 0 )
    \/
    ( ( P69B4Dist C B ) = 0 )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      ( P69B4Dot A B C )
      /
      (
        ( P69B4Dist A B )
        x.
        ( P69B4Dist C B )
      )
    )
  )
) $.

${
  $d S i w x z $.

  p69b4-hull-definition $a |- (
    P69B4Hull S
  ) = {
    z e. P69B4R2 |
    E. w
      (
        (
          w : S --> RR
          /\
          A. x e. S 0 <_ ( w ` x )
        )
        /\
        (
          ( sum_ x e. S ( w ` x ) ) = 1
          /\
          z =
            (
              i e. P69B4I |->
                sum_ x e. S
                  (
                    ( w ` x )
                    x.
                    ( x ` i )
                  )
            )
        )
      )
  } $.
$}

${
  p69b4-continuous-definition $a |- (
    ( P69B4Continuous G )
    <->
    (
      ( G |` ( 0 [,] 1 ) ) e.
        (
          ( ( TopOpen ` RRfld ) |`t ( 0 [,] 1 ) )
          Cn
          P69B4Top
        )
    )
  ) $.
$}

${
  $d G j k n p s $.

  p69b4-variation-definition $a |- (
    ( P69B4Variation G )
    =
    sup
      (
        { s e. RR |
          E. n e. NN E. p
            (
              (
                p : ( 0 ... n ) --> RR
                /\
                ( ( p ` 0 ) = 0 /\ ( p ` n ) = 1 )
              )
              /\
              (
                A. j e. ( 0 ..^ n )
                  ( p ` j ) < ( p ` ( j + 1 ) )
                /\
                s =
                  sum_ k e. ( 0 ..^ n )
                    (
                      P69B4Dist
                        ( G ` ( p ` ( k + 1 ) ) )
                        ( G ` ( p ` k ) )
                    )
              )
            )
        } ,
        RR ,
        <
      )
  ) $.
$}

${
  $d A B C D G $.

  putnambench-putnam-1969-b4 $a |-
    A. G e. ( P69B4R2 ^m RR )
      (
        (
          ( P69B4Continuous G )
          /\
          ( P69B4Variation G ) = 1
        )
        ->
        E. A e. P69B4R2
        E. B e. P69B4R2
        E. C e. P69B4R2
        E. D e. P69B4R2
          (
            ( G " ( 0 [,] 1 ) )
              C_ ( P69B4Hull ( { A , B } u. { C , D } ) )
            /\
            (
              (
                ( P69B4Dist A B )
                x.
                ( P69B4Dist B C )
              )
              =
              ( 1 / 4 )
              /\
              (
                ( P69B4Angle A B C ) = ( _pi / 2 )
                /\
                (
                  ( P69B4Angle B C D ) = ( _pi / 2 )
                  /\
                  (
                    ( P69B4Angle C D A ) = ( _pi / 2 )
                    /\
                    ( P69B4Angle D A B ) = ( _pi / 2 )
                  )
                )
              )
            )
          )
      )
  $.
$}
