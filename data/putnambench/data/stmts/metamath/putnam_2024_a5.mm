$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_a5: the probability that a random chord of the radius-nine
  circle intersects the unit disk centered at (r,0) is minimized for
  0 <= r <= 8 exactly when r = 0. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P24A5I is the two-coordinate index set and P24A5R2 is the real coordinate
  plane. P24A5CirclePoint parametrizes the radius-nine circle by a uniform
  parameter in [0,1].

  P24A5Intersects says that the full affine line through P and Q contains a
  point on the unit sphere centered at (r,0), exactly matching the designated
  Lean source. P24A5Event is the full set of independent parameter pairs in
  [0,1]^2 satisfying that condition, and P24A5Probability is its
  two-dimensional Lebesgue measure through set.mm's voln.

  Since [0,8] is nonempty and each displayed candidate r belongs to it,
  comparison with every value on [0,8] is bidirectionally equivalent to the
  source's equality with the infimum over that interval. The final assertion
  states that the complete set of minimizers is the annotated solution {0}.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c P24A5I P24A5R2 P24A5CirclePoint P24A5Intersects
   P24A5Event P24A5Probability $.

p24a5-index-syntax $a class P24A5I $.
p24a5-plane-syntax $a class P24A5R2 $.
p24a5-circle-point-syntax $a class ( P24A5CirclePoint s ) $.
p24a5-intersects-syntax $a wff ( P24A5Intersects r P Q ) $.
p24a5-event-syntax $a class ( P24A5Event r ) $.
p24a5-probability-syntax $a class ( P24A5Probability r ) $.

p24a5-index-definition $a |- P24A5I = ( 1 ... 2 ) $.

p24a5-plane-definition $a |- P24A5R2 = ( RR ^m P24A5I ) $.

${
  $d j s $.

  p24a5-circle-point-definition $a |- (
    P24A5CirclePoint s
  ) = (
    j e. P24A5I |->
      if (
        j = 1 ,
        (
          9
          x.
          (
            cos
            `
            ( ( 2 x. _pi ) x. s )
          )
        ) ,
        (
          9
          x.
          (
            sin
            `
            ( ( 2 x. _pi ) x. s )
          )
        )
      )
  ) $.
$}

${
  $d P Q r u $.

  p24a5-intersects-definition $a |- (
    ( P24A5Intersects r P Q )
    <->
    E. u e. RR
      (
        (
          (
            (
              (
                ( P ` 1 )
                +
                (
                  u
                  x.
                  ( ( Q ` 1 ) - ( P ` 1 ) )
                )
              )
              -
              r
            )
            ^ 2
          )
          +
          (
            (
              ( P ` 2 )
              +
              (
                u
                x.
                ( ( Q ` 2 ) - ( P ` 2 ) )
              )
            )
            ^ 2
          )
        )
        =
        1
      )
  ) $.
$}

${
  $d r z $.

  p24a5-event-definition $a |- (
    P24A5Event r
  ) = {
    z e. P24A5R2 |
    (
      ( z ` 1 ) e. ( 0 [,] 1 )
      /\
      (
        ( z ` 2 ) e. ( 0 [,] 1 )
        /\
        (
          P24A5Intersects
            r
            ( P24A5CirclePoint ( z ` 1 ) )
            ( P24A5CirclePoint ( z ` 2 ) )
        )
      )
    )
  } $.
$}

p24a5-probability-definition $a |- (
  P24A5Probability r
) = (
  ( voln ` P24A5I )
  `
  ( P24A5Event r )
) $.

${
  $d r x $.

  putnambench-putnam-2024-a5 $a |- {
    r e. RR |
    (
      r e. ( 0 [,] 8 )
      /\
      A. x e. ( 0 [,] 8 )
        ( P24A5Probability r )
        <_
        ( P24A5Probability x )
    )
  } = { 0 } $.
$}
