$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_b3: every twice continuously differentiable real function
  on the plane has, for each pair of radii 0 < r < d, a radius-r disk
  centered distance d from the origin on which the integral of
  y h_x - x h_y is zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P21B3Index is the two-element coordinate interval {0,1}. P21B3R2 is the
  resulting real coordinate plane, P21B3Top is its standard product topology,
  and P21B3Dist is Euclidean distance.

  P21B3Repl replaces one coordinate of a point. P21B3Slice, P21B3Part,
  P21B3D1, and P21B3D2 use set.mm's native real derivative to form the
  coordinate slices and their first and second partial derivatives.
  P21B3C2 requires every such partial to exist throughout the plane and
  requires all partials of orders one and two to be continuous there.
  On the open domain R^2 this is equivalent to twice continuous
  differentiability.

  P21B3Rho is exactly y h_x - x h_y. P21B3Ball is the open Euclidean disk.
  P21B3Integral is its iterated real Lebesgue integral, using the disk's
  vertical slices. For the continuous integrand supplied by P21B3C2,
  Fubini's theorem makes this equal to the source's two-dimensional
  Lebesgue integral over P21B3Ball.

  The final biconditional retains the annotated source answer True as T.
  Every declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c
  P21B3Index P21B3R2 P21B3Top P21B3Zero P21B3Vec P21B3Dist P21B3Repl
  P21B3Slice P21B3Part P21B3D1 P21B3D2 P21B3C2
  P21B3Rho P21B3Ball P21B3Integral
$.

p21b3-index-syntax $a class P21B3Index $.
p21b3-plane-syntax $a class P21B3R2 $.
p21b3-topology-syntax $a class P21B3Top $.
p21b3-zero-syntax $a class P21B3Zero $.
p21b3-vector-syntax $a class ( P21B3Vec x y ) $.
p21b3-distance-syntax $a class ( P21B3Dist A B ) $.
p21b3-replace-syntax $a class ( P21B3Repl p i r ) $.
p21b3-slice-syntax $a class ( P21B3Slice F i p ) $.
p21b3-partial-syntax $a class ( P21B3Part F i p ) $.
p21b3-first-partial-syntax $a class ( P21B3D1 F i ) $.
p21b3-second-partial-syntax $a class ( P21B3D2 F i j ) $.
p21b3-c2-syntax $a wff ( P21B3C2 F ) $.
p21b3-rho-syntax $a class ( P21B3Rho F p ) $.
p21b3-ball-syntax $a class ( P21B3Ball c r ) $.
p21b3-integral-syntax $a class ( P21B3Integral F c r ) $.

p21b3-index-definition $a |- P21B3Index = ( 0 ... 1 ) $.

p21b3-plane-definition $a |- P21B3R2 = ( RR ^m P21B3Index ) $.

p21b3-topology-definition $a |- P21B3Top = (
  Xt_ `
    (
      P21B3Index
      X.
      { ( TopOpen ` RRfld ) }
    )
) $.

${
  $d k x y $.

  p21b3-vector-definition $a |- (
    P21B3Vec x y
  ) = (
    k e. P21B3Index |->
      if (
        k = 0 ,
        x ,
        y
      )
  ) $.
$}

p21b3-zero-definition $a |- P21B3Zero = ( P21B3Vec 0 0 ) $.

${
  $d A B k $.

  p21b3-distance-definition $a |- (
    P21B3Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P21B3Index
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d i k p r $.

  p21b3-replace-definition $a |- (
    P21B3Repl p i r
  ) = (
    k e. P21B3Index |->
      if (
        k = i ,
        r ,
        ( p ` k )
      )
  ) $.
$}

${
  $d F i p r $.

  p21b3-slice-definition $a |- (
    P21B3Slice F i p
  ) = (
    r e. RR |->
      (
        F
        `
        ( P21B3Repl p i r )
      )
  ) $.
$}

${
  $d F i p $.

  p21b3-partial-definition $a |- (
    P21B3Part F i p
  ) = if (
    ( p ` i ) e.
      dom
        (
          RR _D
            ( P21B3Slice F i p )
        ) ,
    (
      (
        RR _D
          ( P21B3Slice F i p )
      )
      ` ( p ` i )
    ) ,
    0
  ) $.
$}

${
  $d F i p $.

  p21b3-first-partial-definition $a |- (
    P21B3D1 F i
  ) = (
    p e. P21B3R2 |->
      ( P21B3Part F i p )
  ) $.
$}

${
  $d F i j p $.

  p21b3-second-partial-definition $a |- (
    P21B3D2 F i j
  ) = (
    p e. P21B3R2 |->
      (
        P21B3Part
        ( P21B3D1 F i )
        j
        p
      )
  ) $.
$}

${
  $d F i j p $.

  p21b3-c2-definition $a |- (
    ( P21B3C2 F )
    <->
    (
      F e. ( RR ^m P21B3R2 )
      /\
      (
        A. i e. P21B3Index A. p e. P21B3R2
          ( p ` i ) e.
            dom
              (
                RR _D
                  ( P21B3Slice F i p )
              )
        /\
        (
          A. i e. P21B3Index
            ( P21B3D1 F i )
            e.
            (
              P21B3Top
              Cn
              ( TopOpen ` RRfld )
            )
          /\
          (
            A. i e. P21B3Index A. j e. P21B3Index A. p e. P21B3R2
              ( p ` j ) e.
                dom
                  (
                    RR _D
                      (
                        P21B3Slice
                        ( P21B3D1 F i )
                        j
                        p
                      )
                  )
            /\
            A. i e. P21B3Index A. j e. P21B3Index
              ( P21B3D2 F i j )
              e.
              (
                P21B3Top
                Cn
                ( TopOpen ` RRfld )
              )
          )
        )
      )
    )
  ) $.
$}

p21b3-rho-definition $a |- (
  P21B3Rho F p
) = (
  (
    ( p ` 1 )
    x.
    ( P21B3Part F 0 p )
  )
  -
  (
    ( p ` 0 )
    x.
    ( P21B3Part F 1 p )
  )
) $.

${
  $d c p r $.

  p21b3-ball-definition $a |- (
    P21B3Ball c r
  ) = {
    p e. P21B3R2 |
      ( P21B3Dist p c ) < r
  } $.
$}

${
  $d F c r x y $.

  p21b3-integral-definition $a |- (
    P21B3Integral F c r
  ) = (
    S.
      (
        ( ( c ` 0 ) - r )
        (,)
        ( ( c ` 0 ) + r )
      )
      (
        S.
          (
            (
              ( c ` 1 )
              -
              (
                sqrt
                `
                (
                  ( r ^ 2 )
                  -
                  (
                    (
                      x
                      -
                      ( c ` 0 )
                    )
                    ^ 2
                  )
                )
              )
            )
            (,)
            (
              ( c ` 1 )
              +
              (
                sqrt
                `
                (
                  ( r ^ 2 )
                  -
                  (
                    (
                      x
                      -
                      ( c ` 0 )
                    )
                    ^ 2
                  )
                )
              )
            )
          )
          (
            P21B3Rho
            F
            ( P21B3Vec x y )
          )
          _d y
      )
      _d x
  ) $.
$}

${
  $d c d f r $.

  putnambench-putnam-2021-b3 $a |- (
    (
      A. f e. ( RR ^m P21B3R2 )
        (
          ( P21B3C2 f )
          ->
          A. d e. RR
            (
              0 < d
              ->
              A. r e. RR
                (
                  (
                    0 < r
                    /\
                    r < d
                  )
                  ->
                  E. c e. P21B3R2
                    (
                      ( P21B3Dist c P21B3Zero ) = d
                      /\
                      ( P21B3Integral f c r ) = 0
                    )
                )
            )
        )
    )
    <->
    T.
  ) $.
$}
