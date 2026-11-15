$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_a1: every real-valued function on the real plane whose values
  sum to zero at the four vertices of every nondegenerate square is
  identically zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR X. RR is the full real coordinate plane, and RR ^m ( RR X. RR ) is
  the class of all total real-valued functions on it. The real coordinates
  x and y specify a square's first vertex, while the nonzero real vector
  (u,v) specifies its first side. The other vertices are
  (x+u,y+v), (x+u-v,y+v+u), and (x-v,y+u), exactly as in the coordinate
  ground-truth statements.

  Quantifying the two coordinates is definitionally equivalent to
  quantifying ordered pairs in RR X. RR. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d f u v x y $.

  putnambench-putnam-2009-a1 $a |-
    A. f e. ( RR ^m ( RR X. RR ) )
      (
        A. x e. RR A. y e. RR A. u e. RR A. v e. RR
          (
            -. ( u = 0 /\ v = 0 )
            ->
            (
              (
                (
                  ( f ` <. x , y >. )
                  +
                  ( f ` <. ( x + u ) , ( y + v ) >. )
                )
                +
                (
                  f
                  `
                  <. ( ( x + u ) - v ) , ( ( y + v ) + u ) >.
                )
              )
              +
              ( f ` <. ( x - v ) , ( y + u ) >. )
            )
            =
            0
          )
        ->
        A. x e. RR A. y e. RR
          ( f ` <. x , y >. ) = 0
      )
  $.
$}
