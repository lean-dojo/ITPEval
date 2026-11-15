$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_a5: nonexistence of a continuously differentiable real
  three-dimensional vector field with zero curl off the origin and a
  prescribed rational trace on the coordinate plane. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P87A5I is the coordinate set 1 ... 3, P87A5V3 is the full real
  three-dimensional coordinate space, and P87A5Top is its standard finite
  product topology. P87A5Punctured removes only the zero vector.

  P87A5Repl replaces one coordinate, P87A5Slice is the resulting
  real-valued one-variable component slice, and P87A5Part is its native
  set.mm derivative at the original coordinate. The zero fallback makes the
  partial-derivative operator total and is inactive under P87A5C1.
  P87A5C1 requires all first coordinate partials to exist on the punctured
  space and their restrictions to be continuous there. Since the punctured
  space is open in finite-dimensional real space, this is equivalent to the
  source's C1 condition.

  P87A5CurlZero expands the three coordinate equations for zero curl.
  P87A5Trace inlines the uniquely specified source function G, eliminating
  only its definitional parameter. Its two quotients are explicitly
  totalized to zero when the common denominator vanishes, matching Lean,
  Rocq, HOL Light, and the PVS safe_div definition at (0,0). The final
  biconditional retains the annotated source solution False as F. All
  declarations are unproved $a statement encodings; this database contains
  no $p declaration.
$)

$c
  P87A5I P87A5V3 P87A5Top P87A5Zero P87A5Punctured
  P87A5Repl P87A5Vec P87A5Slice P87A5Part P87A5D1
  P87A5C1 P87A5CurlZero P87A5Trace
$.

p87a5-index-syntax $a class P87A5I $.
p87a5-vector-space-syntax $a class P87A5V3 $.
p87a5-vector-topology-syntax $a class P87A5Top $.
p87a5-zero-vector-syntax $a class P87A5Zero $.
p87a5-punctured-space-syntax $a class P87A5Punctured $.
p87a5-replace-syntax $a class ( P87A5Repl x i r ) $.
p87a5-vector-syntax $a class ( P87A5Vec x y z ) $.
p87a5-slice-syntax $a class ( P87A5Slice F i j x ) $.
p87a5-partial-syntax $a class ( P87A5Part F i j x ) $.
p87a5-first-partial-function-syntax $a class ( P87A5D1 F i j ) $.
p87a5-c1-syntax $a wff ( P87A5C1 F ) $.
p87a5-zero-curl-syntax $a wff ( P87A5CurlZero F ) $.
p87a5-trace-syntax $a wff ( P87A5Trace F ) $.

p87a5-index-definition $a |- P87A5I = ( 1 ... 3 ) $.

p87a5-vector-space-definition $a |- P87A5V3 = ( RR ^m P87A5I ) $.

p87a5-vector-topology-definition $a |- P87A5Top = (
  Xt_ `
    (
      P87A5I
      X.
      { ( TopOpen ` RRfld ) }
    )
) $.

${
  p87a5-zero-vector-definition $a |- P87A5Zero = (
    k e. P87A5I |-> 0
  ) $.
$}

p87a5-punctured-space-definition $a |- P87A5Punctured = (
  P87A5V3 \ { P87A5Zero }
) $.

${
  $d i k r x $.

  p87a5-replace-definition $a |- (
    P87A5Repl x i r
  ) = (
    k e. P87A5I |->
      if (
        k = i ,
        r ,
        ( x ` k )
      )
  ) $.
$}

${
  $d k x y z $.

  p87a5-vector-definition $a |- (
    P87A5Vec x y z
  ) = (
    k e. P87A5I |->
      if (
        k = 1 ,
        x ,
        if (
          k = 2 ,
          y ,
          z
        )
      )
  ) $.
$}

${
  $d F i j r x $.

  p87a5-slice-definition $a |- (
    P87A5Slice F i j x
  ) = (
    r e. RR |->
      (
        (
          F
          `
          ( P87A5Repl x j r )
        )
        ` i
      )
  ) $.
$}

${
  $d F i j x $.

  p87a5-partial-definition $a |- (
    P87A5Part F i j x
  ) = if (
    ( x ` j ) e.
      dom
        (
          RR _D
            ( P87A5Slice F i j x )
        ) ,
    (
      (
        RR _D
          ( P87A5Slice F i j x )
      )
      ` ( x ` j )
    ) ,
    0
  ) $.
$}

${
  $d F i j x $.

  p87a5-first-partial-function-definition $a |- (
    P87A5D1 F i j
  ) = (
    x e. P87A5V3 |->
      ( P87A5Part F i j x )
  ) $.
$}

${
  $d F i j x $.

  p87a5-c1-definition $a |- (
    ( P87A5C1 F )
    <->
    (
      F e. ( P87A5V3 ^m P87A5V3 )
      /\
      (
        A. i e. P87A5I
          A. j e. P87A5I
            A. x e. P87A5Punctured
              ( x ` j ) e.
                dom
                  (
                    RR _D
                      ( P87A5Slice F i j x )
                  )
        /\
        A. i e. P87A5I
          A. j e. P87A5I
            (
              ( P87A5D1 F i j )
              |`
              P87A5Punctured
            )
            e.
            (
              ( P87A5Top |`t P87A5Punctured )
              Cn
              ( TopOpen ` RRfld )
            )
      )
    )
  ) $.
$}

${
  $d F x $.

  p87a5-zero-curl-definition $a |- (
    ( P87A5CurlZero F )
    <->
    A. x e. P87A5Punctured
      (
        (
          ( P87A5Part F 3 2 x )
          -
          ( P87A5Part F 2 3 x )
        )
        =
        0
        /\
        (
          (
            ( P87A5Part F 1 3 x )
            -
            ( P87A5Part F 3 1 x )
          )
          =
          0
          /\
          (
            (
              ( P87A5Part F 2 1 x )
              -
              ( P87A5Part F 1 2 x )
            )
            =
            0
          )
        )
      )
  ) $.
$}

${
  $d F x y $.

  p87a5-trace-definition $a |- (
    ( P87A5Trace F )
    <->
    A. x e. RR
      A. y e. RR
        (
          F
          `
          ( P87A5Vec x y 0 )
        )
        =
        (
          P87A5Vec
            if (
              (
                ( x ^ 2 )
                +
                ( 4 x. ( y ^ 2 ) )
              )
              =
              0 ,
              0 ,
              (
                ( -u y )
                /
                (
                  ( x ^ 2 )
                  +
                  ( 4 x. ( y ^ 2 ) )
                )
              )
            )
            if (
              (
                ( x ^ 2 )
                +
                ( 4 x. ( y ^ 2 ) )
              )
              =
              0 ,
              0 ,
              (
                x
                /
                (
                  ( x ^ 2 )
                  +
                  ( 4 x. ( y ^ 2 ) )
                )
              )
            )
            0
        )
  ) $.
$}

${
  putnambench-putnam-1987-a5 $a |- (
    E. f e. ( P87A5V3 ^m P87A5V3 )
      (
        ( P87A5C1 f )
        /\
        (
          ( P87A5CurlZero f )
          /\
          ( P87A5Trace f )
        )
      )
    <->
    F.
  ) $.
$}
