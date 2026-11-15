$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_b5: a closed convex planar set containing no nonzero lattice
  point and having equal Lebesgue area in the four quadrants has total area
  at most four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P79B5R2 is the real coordinate plane with its standard finite product
  topology P79B5Top. P79B5Point forms the point with the displayed first and
  second coordinates, P79B5Convex expands real convexity coordinatewise, and
  P79B5Area is two-dimensional Lebesgue measure through set.mm's
  finite-dimensional volume function voln. The four quadrant classes include
  their boundary axes, exactly as in the ground-truth sources.

  The final declaration is the single unproved $a corpus statement. It keeps
  the planar set arbitrary, quantifies over all integer-coordinate points, and
  states all four quadrant-area equalities; this database contains no $p proof
  statement.
$)

$c P79B5I P79B5R2 P79B5Top P79B5Point P79B5Zero $.
$c P79B5Convex P79B5Area P79B5QPP P79B5QPN P79B5QNP P79B5QNN $.

p79b5-index-syntax $a class P79B5I $.
p79b5-plane-syntax $a class P79B5R2 $.
p79b5-topology-syntax $a class P79B5Top $.
p79b5-point-syntax $a class ( P79B5Point A B ) $.
p79b5-zero-syntax $a class P79B5Zero $.
p79b5-convex-syntax $a wff ( P79B5Convex A ) $.
p79b5-area-syntax $a class ( P79B5Area A ) $.
p79b5-first-quadrant-syntax $a class P79B5QPP $.
p79b5-fourth-quadrant-syntax $a class P79B5QPN $.
p79b5-second-quadrant-syntax $a class P79B5QNP $.
p79b5-third-quadrant-syntax $a class P79B5QNN $.

p79b5-index-definition $a |- P79B5I = ( 1 ... 2 ) $.

p79b5-plane-definition $a |- P79B5R2 = ( RR ^m P79B5I ) $.

p79b5-topology-definition $a |- P79B5Top =
  (
    Xt_ `
      ( P79B5I X. { ( topGen ` ran (,) ) } )
  )
$.

${
  $d A B j $.

  p79b5-point-definition $a |- (
    P79B5Point A B
  ) = (
    j e. P79B5I |->
      if ( j = 1 , A , B )
  ) $.
$}

p79b5-zero-definition $a |- P79B5Zero =
  ( P79B5Point 0 0 )
$.

${
  $d A j t x y $.

  p79b5-convex-definition $a |- (
    ( P79B5Convex A )
    <->
    (
      A C_ P79B5R2
      /\
      A. x e. A A. y e. A A. t e. ( 0 [,] 1 )
        (
          j e. P79B5I |->
            (
              ( ( 1 - t ) x. ( x ` j ) )
              +
              ( t x. ( y ` j ) )
            )
        )
        e. A
    )
  ) $.
$}

p79b5-area-definition $a |- (
  P79B5Area A
) = (
  ( voln ` P79B5I )
  `
  A
) $.

p79b5-first-quadrant-definition $a |- P79B5QPP = {
  z e. P79B5R2 |
    (
      0 <_ ( z ` 1 )
      /\
      0 <_ ( z ` 2 )
    )
} $.

p79b5-fourth-quadrant-definition $a |- P79B5QPN = {
  z e. P79B5R2 |
    (
      0 <_ ( z ` 1 )
      /\
      ( z ` 2 ) <_ 0
    )
} $.

p79b5-second-quadrant-definition $a |- P79B5QNP = {
  z e. P79B5R2 |
    (
      ( z ` 1 ) <_ 0
      /\
      0 <_ ( z ` 2 )
    )
} $.

p79b5-third-quadrant-definition $a |- P79B5QNN = {
  z e. P79B5R2 |
    (
      ( z ` 1 ) <_ 0
      /\
      ( z ` 2 ) <_ 0
    )
} $.

${
  $d a b c $.

  putnambench-putnam-1979-b5 $a |- A. c e. ~P P79B5R2
    (
      (
        (
          c e. ( Clsd ` P79B5Top )
          /\
          (
            ( P79B5Convex c )
            /\
            P79B5Zero e. c
          )
        )
        /\
        (
          A. a e. ZZ A. b e. ZZ
            (
              (
                a =/= 0
                \/
                b =/= 0
              )
              ->
              -. ( P79B5Point a b ) e. c
            )
          /\
          (
            ( P79B5Area ( c i^i P79B5QPP ) )
            =
            ( P79B5Area ( c i^i P79B5QPN ) )
            /\
            (
              ( P79B5Area ( c i^i P79B5QPN ) )
              =
              ( P79B5Area ( c i^i P79B5QNP ) )
              /\
              ( P79B5Area ( c i^i P79B5QNP ) )
              =
              ( P79B5Area ( c i^i P79B5QNN ) )
            )
          )
        )
      )
      ->
      ( P79B5Area c ) <_ 4
    )
  $.
$}
