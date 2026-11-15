$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_a6: the affirmative assertion that a continuous real function
  on the unit square is zero when its integral over every centered square
  reaching the boundary is zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P77A6Edge(t) is min(t,1-t), and P77A6Room(x,y) is the minimum of the
  four distances x, 1-x, y, and 1-y from a point of the unit square to its
  sides. P77A6Continuous(f) expands global joint continuity of a total
  real-valued function on RR X. RR in epsilon-delta form; coordinatewise
  delta neighborhoods induce the standard product topology.

  The nested Lebesgue integrals are over the closed centered square with
  radius P77A6Room(x,y). For continuous functions this iterated integral is
  equal to the product-measure integral used by the Isabelle source.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P77A6Edge P77A6Room P77A6Continuous $.

p77a6-edge-syntax $a class ( P77A6Edge x ) $.
p77a6-room-syntax $a class ( P77A6Room x y ) $.
p77a6-continuous-syntax $a wff ( P77A6Continuous F ) $.

p77a6-edge-definition $a |- (
  ( P77A6Edge x )
  =
  if (
    x <_ ( 1 - x ) ,
    x ,
    ( 1 - x )
  )
) $.

${
  $d x y $.

  p77a6-room-definition $a |- (
    ( P77A6Room x y )
    =
    if (
      ( P77A6Edge x ) <_ ( P77A6Edge y ) ,
      ( P77A6Edge x ) ,
      ( P77A6Edge y )
    )
  ) $.
$}

${
  $d d e f u v x y $.

  p77a6-continuous-definition $a |- (
    ( P77A6Continuous f )
    <->
    A. x e. RR A. y e. RR A. e e. RR
      (
        0 < e
        ->
        E. d e. RR
          (
            0 < d
            /\
            A. u e. RR A. v e. RR
              (
                (
                  ( abs ` ( u - x ) ) < d
                  /\
                  ( abs ` ( v - y ) ) < d
                )
                ->
                (
                  abs
                  `
                  (
                    ( f ` <. u , v >. )
                    -
                    ( f ` <. x , y >. )
                  )
                )
                < e
              )
          )
      )
  ) $.
$}

${
  $d f u v x y $.

  putnambench-putnam-1977-a6 $a |-
    A. f e. ( RR ^m ( RR X. RR ) )
      (
        ( P77A6Continuous f )
        ->
        (
          (
            A. x e. ( 0 [,] 1 ) A. y e. ( 0 [,] 1 )
              (
                S.
                  (
                    ( x - ( P77A6Room x y ) )
                    [,]
                    ( x + ( P77A6Room x y ) )
                  )
                  (
                    S.
                      (
                        ( y - ( P77A6Room x y ) )
                        [,]
                        ( y + ( P77A6Room x y ) )
                      )
                      ( f ` <. u , v >. )
                      _d v
                  )
                  _d u
              )
              =
              0
          )
          ->
          A. x e. ( 0 [,] 1 ) A. y e. ( 0 [,] 1 )
            ( f ` <. x , y >. ) = 0
        )
      )
  $.
$}
