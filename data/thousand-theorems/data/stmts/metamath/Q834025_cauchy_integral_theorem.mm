$(
  Statement-only formalization of Thousand Theorems corpus artifact Q834025
  (thousand-theorems__metamath__Q834025), "Cauchy integral theorem": Cauchy's
  integral formula for a complex-valued function continuous on a closed disk
  and complex differentiable in its interior away from a countable set. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q834025OpenBall and Q834025ClosedBall are the open and closed disks in CC.
  Q834025ContinuousOn is relative epsilon-delta continuity. Membership of z
  in dom ( CC _D F ) is SetMM's native complex differentiability predicate,
  equivalent here to Lean's one-dimensional complex Frechet
  differentiability.

  Q834025CircleMap parametrizes the circle by
  c + R * exp(i*t), and Q834025CircleDeriv is its derivative.
  Q834025CircleIntegral is the directed totalized complex Lebesgue integral
  from 0 to 2*pi of F(z)/(z-w) times dz/dt. This is the SetMM rendering of
  Lean's circleIntegral, including its behavior for arbitrary real radii.

  The final $a assertion quantifies over the arbitrary real radius, complex
  center and interior point, countable exceptional set, and total complex
  function. Every preceding $a declaration is syntax or an explicit
  definition; there is no $p proof statement.
$)

$c Q834025OpenBall Q834025ClosedBall Q834025ContinuousOn
   Q834025CircleMap Q834025CircleDeriv Q834025CircleIntegral $.

q834025-open-ball-syntax
  $a class ( Q834025OpenBall C R ) $.
q834025-closed-ball-syntax
  $a class ( Q834025ClosedBall C R ) $.
q834025-continuous-on-syntax
  $a wff ( Q834025ContinuousOn F S ) $.
q834025-circle-map-syntax
  $a class ( Q834025CircleMap C R T ) $.
q834025-circle-deriv-syntax
  $a class ( Q834025CircleDeriv R T ) $.
q834025-circle-integral-syntax
  $a class ( Q834025CircleIntegral F C R W ) $.

${
  $d C R z $.

  q834025-open-ball-definition $a |- (
    Q834025OpenBall C R
  ) = {
    z e. CC |
      ( ( abs ` ( z - C ) ) < R )
  } $.
$}

${
  $d C R z $.

  q834025-closed-ball-definition $a |- (
    Q834025ClosedBall C R
  ) = {
    z e. CC |
      ( ( abs ` ( z - C ) ) <_ R )
  } $.
$}

${
  $d F S d e x y $.

  q834025-continuous-on-definition $a |- (
    ( Q834025ContinuousOn F S )
    <->
    A. x e. S
      A. e e. RR+
        E. d e. RR+
          A. y e. S
            (
              ( ( abs ` ( y - x ) ) < d )
              ->
              (
                ( abs ` ( ( F ` y ) - ( F ` x ) ) )
                <
                e
              )
            )
  ) $.
$}

${
  $d C R T $.

  q834025-circle-map-definition $a |- (
    Q834025CircleMap C R T
  ) = (
    C
    +
    ( R x. ( exp ` ( _i x. T ) ) )
  ) $.
$}

${
  $d R T $.

  q834025-circle-deriv-definition $a |- (
    Q834025CircleDeriv R T
  ) = (
    ( R x. _i )
    x.
    ( exp ` ( _i x. T ) )
  ) $.
$}

${
  $d C F R W t $.

  q834025-circle-integral-definition $a |- (
    Q834025CircleIntegral F C R W
  ) = (
    S_ [ 0 -> ( 2 x. _pi ) ]
      (
        (
          ( F ` ( Q834025CircleMap C R t ) )
          /
          ( ( Q834025CircleMap C R t ) - W )
        )
        x.
        ( Q834025CircleDeriv R t )
      )
    _d t
  ) $.
$}

${
  $d C F R S W z $.

  thousand-theorems-q834025-cauchy-integral-formula $a |-
    A. R e. RR
      A. C e. CC
        A. W e. CC
          A. S e. ~P CC
            A. F e. ( CC ^m CC )
              (
                (
                  S ~<_ _om
                  /\
                  W e. ( Q834025OpenBall C R )
                  /\
                  (
                    Q834025ContinuousOn
                    F
                    ( Q834025ClosedBall C R )
                  )
                  /\
                  A. z e.
                    ( ( Q834025OpenBall C R ) \ S )
                    z e. dom ( CC _D F )
                )
                ->
                (
                  Q834025CircleIntegral F C R W
                )
                =
                (
                  (
                    ( 2 x. _pi )
                    x.
                    _i
                  )
                  x.
                  ( F ` W )
                )
              )
  $.
$}
