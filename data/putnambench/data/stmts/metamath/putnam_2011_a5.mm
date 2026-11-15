$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_a5: a bound on the minimum absolute value of a twice
  continuously differentiable real function at pairs from any finite
  real sequence, under diagonal, decay, and gradient-parallelism
  hypotheses. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P11A5Dx and P11A5Dy are the derivatives of the two coordinate slices of
  F. P11A5Dxx, P11A5Dxy, P11A5Dyx, and P11A5Dyy are the corresponding
  second coordinate partials. Their zero fallbacks make the operators total;
  all fallbacks are inactive under P11A5C2.

  P11A5Cont expands joint continuity on RR X. RR in epsilon-delta form.
  P11A5C2 requires existence and joint continuity of all coordinate partials
  through order two. For real-valued functions on the real plane this is
  equivalent to twice continuous differentiability. The one-variable
  function g uses set.mm's native global order-two C^n class.

  For n >= 2, the finite set of values indexed by distinct members of
  0 ... n is nonempty. Thus saying that one such value is at most C / n is
  equivalent to the source inequality for the minimum over the n + 1 input
  points. The indices remain internally existentially quantified. Every
  declaration is an unproved $a statement encoding.
$)

$c
  P11A5Dx P11A5Dy P11A5Dxx P11A5Dxy P11A5Dyx P11A5Dyy
  P11A5DX P11A5DY P11A5DXX P11A5DXY P11A5DYX P11A5DYY
  P11A5Cont P11A5C2
$.

p11a5-dx-syntax $a class ( P11A5Dx F x y ) $.
p11a5-dy-syntax $a class ( P11A5Dy F x y ) $.
p11a5-dxx-syntax $a class ( P11A5Dxx F x y ) $.
p11a5-dxy-syntax $a class ( P11A5Dxy F x y ) $.
p11a5-dyx-syntax $a class ( P11A5Dyx F x y ) $.
p11a5-dyy-syntax $a class ( P11A5Dyy F x y ) $.
p11a5-dx-function-syntax $a class ( P11A5DX F ) $.
p11a5-dy-function-syntax $a class ( P11A5DY F ) $.
p11a5-dxx-function-syntax $a class ( P11A5DXX F ) $.
p11a5-dxy-function-syntax $a class ( P11A5DXY F ) $.
p11a5-dyx-function-syntax $a class ( P11A5DYX F ) $.
p11a5-dyy-function-syntax $a class ( P11A5DYY F ) $.
p11a5-cont-syntax $a wff ( P11A5Cont F ) $.
p11a5-c2-syntax $a wff ( P11A5C2 F ) $.

${
  $d F t x y $.

  p11a5-dx-definition $a |- ( P11A5Dx F x y ) = if (
    x e. dom ( RR _D ( t e. RR |-> ( F ` <. t , y >. ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( F ` <. t , y >. ) ) ) ` x ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p11a5-dy-definition $a |- ( P11A5Dy F x y ) = if (
    y e. dom ( RR _D ( t e. RR |-> ( F ` <. x , t >. ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( F ` <. x , t >. ) ) ) ` y ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p11a5-dxx-definition $a |- ( P11A5Dxx F x y ) = if (
    x e. dom ( RR _D ( t e. RR |-> ( P11A5Dx F t y ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P11A5Dx F t y ) ) ) ` x ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p11a5-dxy-definition $a |- ( P11A5Dxy F x y ) = if (
    y e. dom ( RR _D ( t e. RR |-> ( P11A5Dx F x t ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P11A5Dx F x t ) ) ) ` y ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p11a5-dyx-definition $a |- ( P11A5Dyx F x y ) = if (
    x e. dom ( RR _D ( t e. RR |-> ( P11A5Dy F t y ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P11A5Dy F t y ) ) ) ` x ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p11a5-dyy-definition $a |- ( P11A5Dyy F x y ) = if (
    y e. dom ( RR _D ( t e. RR |-> ( P11A5Dy F x t ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P11A5Dy F x t ) ) ) ` y ) ,
    0
  ) $.
$}

${
  $d F p $.

  p11a5-dx-function-definition $a |- ( P11A5DX F ) =
    ( p e. ( RR X. RR ) |->
      ( P11A5Dx F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p11a5-dy-function-definition $a |- ( P11A5DY F ) =
    ( p e. ( RR X. RR ) |->
      ( P11A5Dy F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p11a5-dxx-function-definition $a |- ( P11A5DXX F ) =
    ( p e. ( RR X. RR ) |->
      ( P11A5Dxx F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p11a5-dxy-function-definition $a |- ( P11A5DXY F ) =
    ( p e. ( RR X. RR ) |->
      ( P11A5Dxy F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p11a5-dyx-function-definition $a |- ( P11A5DYX F ) =
    ( p e. ( RR X. RR ) |->
      ( P11A5Dyx F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p11a5-dyy-function-definition $a |- ( P11A5DYY F ) =
    ( p e. ( RR X. RR ) |->
      ( P11A5Dyy F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F d e u v x y $.

  p11a5-cont-definition $a |- (
    ( P11A5Cont F )
    <->
    (
      F e. ( RR ^m ( RR X. RR ) )
      /\
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
                      ( F ` <. u , v >. )
                      -
                      ( F ` <. x , y >. )
                    )
                  )
                  < e
                )
            )
        )
    )
  ) $.
$}

${
  $d F t x y $.

  p11a5-c2-definition $a |- (
    ( P11A5C2 F )
    <->
    (
      (
        A. x e. RR A. y e. RR
          (
            x e. dom ( RR _D ( t e. RR |-> ( F ` <. t , y >. ) ) )
            /\
            y e. dom ( RR _D ( t e. RR |-> ( F ` <. x , t >. ) ) )
          )
        /\
        A. x e. RR A. y e. RR
          (
            (
              x e.
                dom ( RR _D ( t e. RR |-> ( P11A5Dx F t y ) ) )
              /\
              y e.
                dom ( RR _D ( t e. RR |-> ( P11A5Dx F x t ) ) )
            )
            /\
            (
              x e.
                dom ( RR _D ( t e. RR |-> ( P11A5Dy F t y ) ) )
              /\
              y e.
                dom ( RR _D ( t e. RR |-> ( P11A5Dy F x t ) ) )
            )
          )
      )
      /\
      (
        (
          ( P11A5Cont F )
          /\
          (
            ( P11A5Cont ( P11A5DX F ) )
            /\
            ( P11A5Cont ( P11A5DY F ) )
          )
        )
        /\
        (
          (
            ( P11A5Cont ( P11A5DXX F ) )
            /\
            ( P11A5Cont ( P11A5DXY F ) )
          )
          /\
          (
            ( P11A5Cont ( P11A5DYX F ) )
            /\
            ( P11A5Cont ( P11A5DYY F ) )
          )
        )
      )
    )
  ) $.
$}

${
  $d c d f g h i j n u v x $.

  putnambench-putnam-2011-a5 $a |-
    A. f e. ( RR ^m ( RR X. RR ) )
    A. g e. ( RR ^m RR )
      (
        (
          (
            ( P11A5C2 f )
            /\
            g e. ( ( C^n ` RR ) ` 2 )
          )
          /\
          (
            A. u e. RR ( f ` <. u , u >. ) = 0
            /\
            (
              A. x e. RR
                (
                  0 < ( g ` x )
                  /\
                  ( ( x ^ 2 ) x. ( g ` x ) ) <_ 1
                )
              /\
              A. u e. RR A. v e. RR
                E. c e. RR
                  (
                    ( P11A5Dx f u v ) = ( c x. ( g ` u ) )
                    /\
                    ( P11A5Dy f u v ) = ( c x. ( -u ( g ` v ) ) )
                  )
            )
          )
        )
        ->
        E. d e. RR A. n e. NN
          (
            2 <_ n
            ->
            A. h e. ( RR ^m ( 0 ... n ) )
              E. i e. ( 0 ... n ) E. j e. ( 0 ... n )
                (
                  i =/= j
                  /\
                  (
                    abs
                    `
                    (
                      f
                      `
                      <. ( h ` i ) , ( h ` j ) >.
                    )
                  )
                  <_
                  ( d / n )
                )
          )
      )
  $.
$}
