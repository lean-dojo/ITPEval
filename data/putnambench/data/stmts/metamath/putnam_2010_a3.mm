$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_a3: a bounded continuously differentiable real function on
  the real plane satisfying a constant-coefficient first-order partial
  differential equation is identically zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P10A3Dx and P10A3Dy are the real derivatives of the coordinate slices of
  F at (x,y). Their zero fallbacks make them total, matching Lean's total
  fderiv operator; the fallbacks are inactive under P10A3C1.

  P10A3C1 requires both coordinate derivatives to exist everywhere and the
  two resulting derivative functions to be jointly continuous on RR X. RR.
  Its epsilon-delta clause uses rectangular neighborhoods, which induce the
  standard product topology. For real-valued functions on the real plane,
  this is equivalent to the source hypothesis ContDiff RR 1.

  The final assertion universally quantifies the total function F and the
  real constants a, b, and M. It preserves the pointwise PDE, the global
  absolute-value bound, and the pointwise form of equality with the zero
  function. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c P10A3Dx P10A3Dy P10A3C1 $.

p10a3-dx-syntax $a class ( P10A3Dx F x y ) $.
p10a3-dy-syntax $a class ( P10A3Dy F x y ) $.
p10a3-c1-syntax $a wff ( P10A3C1 F ) $.

${
  $d F t x y $.

  p10a3-dx-definition $a |- (
    P10A3Dx F x y
  ) = if (
    x e.
      dom
        (
          RR _D
            ( t e. RR |-> ( F ` <. t , y >. ) )
        ) ,
    (
      (
        RR _D
          ( t e. RR |-> ( F ` <. t , y >. ) )
      )
      ` x
    ) ,
    0
  ) $.
$}

${
  $d F t x y $.

  p10a3-dy-definition $a |- (
    P10A3Dy F x y
  ) = if (
    y e.
      dom
        (
          RR _D
            ( t e. RR |-> ( F ` <. x , t >. ) )
        ) ,
    (
      (
        RR _D
          ( t e. RR |-> ( F ` <. x , t >. ) )
      )
      ` y
    ) ,
    0
  ) $.
$}

${
  $d F d e t u v x y $.

  p10a3-c1-definition $a |- (
    ( P10A3C1 F )
    <->
    (
      F e. ( RR ^m ( RR X. RR ) )
      /\
      (
        A. x e. RR A. y e. RR
          (
            x e.
              dom
                (
                  RR _D
                    ( t e. RR |-> ( F ` <. t , y >. ) )
                )
            /\
            y e.
              dom
                (
                  RR _D
                    ( t e. RR |-> ( F ` <. x , t >. ) )
                )
          )
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
                      (
                        abs
                        `
                        (
                          ( P10A3Dx F u v )
                          -
                          ( P10A3Dx F x y )
                        )
                      )
                      < e
                      /\
                      (
                        abs
                        `
                        (
                          ( P10A3Dy F u v )
                          -
                          ( P10A3Dy F x y )
                        )
                      )
                      < e
                    )
                  )
              )
          )
      )
    )
  ) $.
$}

${
  $d F M a b x y $.

  putnambench-putnam-2010-a3 $a |-
    A. F e. ( RR ^m ( RR X. RR ) )
      A. a e. RR A. b e. RR A. M e. RR
        (
          (
            (
              ( P10A3C1 F )
              /\
              A. x e. RR A. y e. RR
                (
                  ( F ` <. x , y >. )
                  =
                  (
                    ( a x. ( P10A3Dx F x y ) )
                    +
                    ( b x. ( P10A3Dy F x y ) )
                  )
                )
            )
            /\
            A. x e. RR A. y e. RR
              ( abs ` ( F ` <. x , y >. ) ) <_ M
          )
          ->
          A. x e. RR A. y e. RR
            ( F ` <. x , y >. ) = 0
        )
  $.
$}
