$(
  Statement-only formalization of PutnamBench artifact putnam_1962_b3:
  a convex subset of the real Euclidean plane that contains the origin,
  satisfies the stated interior-or-closed condition, and omits a point on
  every ray from the origin is bounded. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P62B3R2 is the real coordinate plane and P62B3Top is its standard finite
  product topology. P62B3Convex expands real convexity coordinatewise,
  P62B3SameRay says that the second vector is a positive scalar multiple
  of the first, and P62B3Bounded gives a uniform Euclidean norm bound.

  In the final assertion, this is equivalent to Mathlib's SameRay relation:
  zero belongs to S while Q does not, so the scalar cannot be zero. The final
  declaration is an unproved $a statement.
$)

$c P62B3I P62B3R2 P62B3Top P62B3Zero $.
$c P62B3Norm P62B3Convex P62B3SameRay P62B3Bounded $.

p62b3-index-syntax $a class P62B3I $.
p62b3-plane-syntax $a class P62B3R2 $.
p62b3-topology-syntax $a class P62B3Top $.
p62b3-zero-syntax $a class P62B3Zero $.
p62b3-norm-syntax $a class ( P62B3Norm A ) $.
p62b3-convex-syntax $a wff ( P62B3Convex A ) $.
p62b3-same-ray-syntax $a wff ( P62B3SameRay P Q ) $.
p62b3-bounded-syntax $a wff ( P62B3Bounded A ) $.

p62b3-index-definition $a |- P62B3I = ( 1 ... 2 ) $.

p62b3-plane-definition $a |- P62B3R2 = ( RR ^m P62B3I ) $.

p62b3-topology-definition $a |- P62B3Top =
  (
    Xt_ `
      ( P62B3I X. { ( topGen ` ran (,) ) } )
  )
$.

p62b3-zero-definition $a |- P62B3Zero =
  ( j e. P62B3I |-> 0 )
$.

${
  $d A j $.

  p62b3-norm-definition $a |- (
    P62B3Norm A
  ) = (
    sqrt `
      sum_ j e. P62B3I
        ( ( A ` j ) ^ 2 )
  ) $.
$}

${
  $d A j t x y $.

  p62b3-convex-definition $a |- (
    ( P62B3Convex A )
    <->
    (
      A C_ P62B3R2
      /\
      A. x e. A A. y e. A A. t e. ( 0 [,] 1 )
        (
          j e. P62B3I |->
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

${
  $d j k P Q $.

  p62b3-same-ray-definition $a |- (
    ( P62B3SameRay P Q )
    <->
    E. k e. RR
      (
        0 < k
        /\
        Q =
          (
            j e. P62B3I |->
              ( k x. ( P ` j ) )
          )
      )
  ) $.
$}

${
  $d A R x $.

  p62b3-bounded-definition $a |- (
    ( P62B3Bounded A )
    <->
    E. R e. RR
      (
        0 < R
        /\
        A. x e. A ( P62B3Norm x ) <_ R
      )
  ) $.
$}

${
  $d P Q S $.

  putnambench-putnam-1962-b3 $a |- A. S
    (
      (
        (
          ( P62B3Convex S )
          /\
          P62B3Zero e. S
        )
        /\
        (
          (
            P62B3Zero e. ( ( int ` P62B3Top ) ` S )
            \/
            S e. ( Clsd ` P62B3Top )
          )
          /\
          A. P e. P62B3R2
            (
              P =/= P62B3Zero
              ->
              E. Q e. P62B3R2
                (
                  ( P62B3SameRay P Q )
                  /\
                  -. Q e. S
                )
            )
        )
      )
      ->
      ( P62B3Bounded S )
    )
  $.
$}
