$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_b4: the infimum of the mixed unit-square difference for any
  twice continuously differentiable real solution of the specified
  two-variable differential equations equals the specified real solution
  constant, independently of the function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions on RR X. RR. P19B4Dx and
  P19B4Dy are its coordinate derivatives, and P19B4Dxx, P19B4Dxy,
  P19B4Dyx, and P19B4Dyy are the corresponding second coordinate partials.
  Their zero fallbacks make them total, while the fallbacks are inactive on
  the closed quadrant under P19B4C2Q.

  P19B4ContQ is joint continuity relative to x >= 1 and y >= 1, expressed
  with rectangular neighborhoods. P19B4C2Q requires existence and relative
  joint continuity of all coordinate partials through order two there, the
  coordinate characterization of twice continuous differentiability on the
  source quadrant.

  P19B4Values F is exactly the set of mixed differences

    F(s+1,s+1) - F(s+1,s) - F(s,s+1) + F(s,s)

  for real s >= 1. Its real-order infimum is the sInf/minimum quantity in
  the formal and informal sources. Ordered pairs replace the source's
  two-coordinate vectors definitionally.

  The final assertion uses the resolved value 2 log(2) - 1/2 recorded by the
  Lean annotation and the explicit Rocq formalization. All auxiliary assertions
  below are syntax or definitions; the final declaration is the single unproved
  $a corpus statement, and this database contains no $p proof declaration.
$)

$c
  P19B4Dx P19B4Dy P19B4Dxx P19B4Dxy P19B4Dyx P19B4Dyy
  P19B4DX P19B4DY P19B4DXX P19B4DXY P19B4DYX P19B4DYY
  P19B4ContQ P19B4C2Q P19B4Values
$.

p19b4-dx-syntax $a class ( P19B4Dx F x y ) $.
p19b4-dy-syntax $a class ( P19B4Dy F x y ) $.
p19b4-dxx-syntax $a class ( P19B4Dxx F x y ) $.
p19b4-dxy-syntax $a class ( P19B4Dxy F x y ) $.
p19b4-dyx-syntax $a class ( P19B4Dyx F x y ) $.
p19b4-dyy-syntax $a class ( P19B4Dyy F x y ) $.
p19b4-dx-function-syntax $a class ( P19B4DX F ) $.
p19b4-dy-function-syntax $a class ( P19B4DY F ) $.
p19b4-dxx-function-syntax $a class ( P19B4DXX F ) $.
p19b4-dxy-function-syntax $a class ( P19B4DXY F ) $.
p19b4-dyx-function-syntax $a class ( P19B4DYX F ) $.
p19b4-dyy-function-syntax $a class ( P19B4DYY F ) $.
p19b4-contq-syntax $a wff ( P19B4ContQ F ) $.
p19b4-c2q-syntax $a wff ( P19B4C2Q F ) $.
p19b4-values-syntax $a class ( P19B4Values F ) $.

${
  $d F t x y $.

  p19b4-dx-definition $a |- ( P19B4Dx F x y ) = if (
    x e. dom ( RR _D ( t e. RR |-> ( F ` <. t , y >. ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( F ` <. t , y >. ) ) ) ` x ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p19b4-dy-definition $a |- ( P19B4Dy F x y ) = if (
    y e. dom ( RR _D ( t e. RR |-> ( F ` <. x , t >. ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( F ` <. x , t >. ) ) ) ` y ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p19b4-dxx-definition $a |- ( P19B4Dxx F x y ) = if (
    x e. dom ( RR _D ( t e. RR |-> ( P19B4Dx F t y ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P19B4Dx F t y ) ) ) ` x ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p19b4-dxy-definition $a |- ( P19B4Dxy F x y ) = if (
    y e. dom ( RR _D ( t e. RR |-> ( P19B4Dx F x t ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P19B4Dx F x t ) ) ) ` y ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p19b4-dyx-definition $a |- ( P19B4Dyx F x y ) = if (
    x e. dom ( RR _D ( t e. RR |-> ( P19B4Dy F t y ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P19B4Dy F t y ) ) ) ` x ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p19b4-dyy-definition $a |- ( P19B4Dyy F x y ) = if (
    y e. dom ( RR _D ( t e. RR |-> ( P19B4Dy F x t ) ) ) ,
    ( ( RR _D ( t e. RR |-> ( P19B4Dy F x t ) ) ) ` y ) ,
    0
  ) $.
$}

${
  $d F p $.

  p19b4-dx-function-definition $a |- ( P19B4DX F ) =
    ( p e. ( RR X. RR ) |->
      ( P19B4Dx F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p19b4-dy-function-definition $a |- ( P19B4DY F ) =
    ( p e. ( RR X. RR ) |->
      ( P19B4Dy F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p19b4-dxx-function-definition $a |- ( P19B4DXX F ) =
    ( p e. ( RR X. RR ) |->
      ( P19B4Dxx F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p19b4-dxy-function-definition $a |- ( P19B4DXY F ) =
    ( p e. ( RR X. RR ) |->
      ( P19B4Dxy F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p19b4-dyx-function-definition $a |- ( P19B4DYX F ) =
    ( p e. ( RR X. RR ) |->
      ( P19B4Dyx F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F p $.

  p19b4-dyy-function-definition $a |- ( P19B4DYY F ) =
    ( p e. ( RR X. RR ) |->
      ( P19B4Dyy F ( 1st ` p ) ( 2nd ` p ) ) ) $.
$}

${
  $d F d e u v x y $.

  p19b4-contq-definition $a |- (
    ( P19B4ContQ F )
    <->
    (
      F e. ( RR ^m ( RR X. RR ) )
      /\
      A. x e. RR A. y e. RR
        (
          (
            1 <_ x
            /\
            1 <_ y
          )
          ->
          A. e e. RR
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
                        (
                          (
                            1 <_ u
                            /\
                            1 <_ v
                          )
                          /\
                          ( abs ` ( u - x ) ) < d
                        )
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
    )
  ) $.
$}

${
  $d F t x y $.

  p19b4-c2q-definition $a |- (
    ( P19B4C2Q F )
    <->
    (
      F e. ( RR ^m ( RR X. RR ) )
      /\
      (
        (
          A. x e. RR A. y e. RR
            (
              (
                1 <_ x
                /\
                1 <_ y
              )
              ->
              (
                x e.
                  dom ( RR _D ( t e. RR |-> ( F ` <. t , y >. ) ) )
                /\
                y e.
                  dom ( RR _D ( t e. RR |-> ( F ` <. x , t >. ) ) )
              )
            )
          /\
          A. x e. RR A. y e. RR
            (
              (
                1 <_ x
                /\
                1 <_ y
              )
              ->
              (
                (
                  x e.
                    dom
                      ( RR _D ( t e. RR |-> ( P19B4Dx F t y ) ) )
                  /\
                  y e.
                    dom
                      ( RR _D ( t e. RR |-> ( P19B4Dx F x t ) ) )
                )
                /\
                (
                  x e.
                    dom
                      ( RR _D ( t e. RR |-> ( P19B4Dy F t y ) ) )
                  /\
                  y e.
                    dom
                      ( RR _D ( t e. RR |-> ( P19B4Dy F x t ) ) )
                )
              )
            )
        )
        /\
        (
          (
            ( P19B4ContQ F )
            /\
            (
              ( P19B4ContQ ( P19B4DX F ) )
              /\
              ( P19B4ContQ ( P19B4DY F ) )
            )
          )
          /\
          (
            (
              ( P19B4ContQ ( P19B4DXX F ) )
              /\
              ( P19B4ContQ ( P19B4DXY F ) )
            )
            /\
            (
              ( P19B4ContQ ( P19B4DYX F ) )
              /\
              ( P19B4ContQ ( P19B4DYY F ) )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d F s z $.

p19b4-values-definition $a |- ( P19B4Values F ) = {
    z e. RR |
      E. s e. RR
        (
          1 <_ s
          /\
          z
          =
          (
            (
              (
                ( F ` <. ( s + 1 ) , ( s + 1 ) >. )
                -
                ( F ` <. ( s + 1 ) , s >. )
              )
              -
              ( F ` <. s , ( s + 1 ) >. )
            )
            +
            ( F ` <. s , s >. )
          )
        )
} $.
$}

${
  $d f x y $.

  putnambench-putnam-2019-b4 $a |-
    A. f e. ( RR ^m ( RR X. RR ) )
      (
        (
          (
            ( P19B4C2Q f )
            /\
            A. x e. RR A. y e. RR
              (
                (
                  1 <_ x
                  /\
                  1 <_ y
                )
                ->
                (
                  (
                    ( x x. ( P19B4Dx f x y ) )
                    +
                    ( y x. ( P19B4Dy f x y ) )
                  )
                  =
                  (
                    ( x x. y )
                    x.
                    ( log ` ( x x. y ) )
                  )
                )
              )
          )
          /\
          A. x e. RR A. y e. RR
            (
              (
                1 <_ x
                /\
                1 <_ y
              )
              ->
              (
                (
                  ( ( x ^ 2 ) x. ( P19B4Dxx f x y ) )
                  +
                  ( ( y ^ 2 ) x. ( P19B4Dyy f x y ) )
                )
                =
                ( x x. y )
              )
            )
        )
        ->
        inf ( ( P19B4Values f ) , RR , < )
        =
        (
          ( 2 x. ( log ` 2 ) )
          -
          ( 1 / 2 )
        )
      )
  $.
$}
