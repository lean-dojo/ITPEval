$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_a6: the right-hand behavior at zero of a twice differentiable
  real function satisfying g(x) / x^r -> 0 for r > 1, namely the dichotomy
  between g'(x) -> 0 and an unbounded second-derivative envelope. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  P19A6Deriv totalizes set.mm's real derivative by assigning zero outside
  its domain. The hypotheses ensure that its values on (0,1) are the actual
  first derivative of F. P19A6SecondDeriv iterates that operation; the
  differentiability hypothesis on P19A6Deriv ensures that its values on
  (0,1) are the actual second derivative.

  P19A6Envelope(F,r,x) is the supremum in the extended reals RR* of
  t^r |F''(t)| for 0 < t <= x. On positive t, set.mm's complex-power
  operation ^c is real-valued and agrees with real exponentiation.

  The two finite right-hand limits are expanded in epsilon-delta form. The
  final at-top condition says that for every real bound M, all sufficiently
  small positive x have envelope greater than M. This is exactly convergence
  of the running extended-real supremum to +oo as x approaches zero from the
  right. The definitions and final declaration are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c P19A6Deriv P19A6SecondDeriv P19A6Envelope $.

p19a6-deriv-syntax $a class ( P19A6Deriv F ) $.
p19a6-second-deriv-syntax $a class ( P19A6SecondDeriv F ) $.
p19a6-envelope-syntax $a class ( P19A6Envelope F r x ) $.

${
  $d F x $.

  p19a6-deriv-definition $a |- ( P19A6Deriv F ) =
    (
      x e. RR |->
        if (
          x e. dom ( RR _D F ) ,
          ( ( RR _D F ) ` x ) ,
          0
        )
    ) $.
$}

p19a6-second-deriv-definition $a |- ( P19A6SecondDeriv F ) =
  ( P19A6Deriv ( P19A6Deriv F ) ) $.

${
  $d F r t x y $.

  p19a6-envelope-definition $a |- ( P19A6Envelope F r x ) =
    sup (
      {
        y e. RR |
          E. t e. ( 0 (,] x )
            y =
            (
              ( t ^c r )
              x.
              (
                abs
                `
                ( ( P19A6SecondDeriv F ) ` t )
              )
            )
      } ,
      RR* ,
      <
    ) $.
$}

${
  $d F M d e r x $.

  putnambench-putnam-2019-a6 $a |-
    A. F e. ( RR ^m RR )
    A. r e. RR
      (
        (
          (
            (
              (
                ( F |` ( 0 [,] 1 ) )
                e.
                ( ( C^n ` ( 0 [,] 1 ) ) ` 0 )
                /\
                ( F |` ( 0 (,) 1 ) )
                e.
                ( ( C^n ` ( 0 (,) 1 ) ) ` 1 )
              )
              /\
              A. x e. ( 0 (,) 1 )
                x e. dom ( RR _D ( P19A6Deriv F ) )
            )
            /\
            1 < r
          )
          /\
          A. e e. RR
            (
              0 < e
              ->
              E. d e. RR
                (
                  0 < d
                  /\
                  A. x e. RR
                    (
                      (
                        0 < x
                        /\
                        x < d
                      )
                      ->
                      (
                        abs
                        `
                        (
                          ( ( F ` x ) / ( x ^c r ) )
                          -
                          0
                        )
                      )
                      < e
                    )
                )
            )
        )
        ->
        (
          A. e e. RR
            (
              0 < e
              ->
              E. d e. RR
                (
                  0 < d
                  /\
                  A. x e. RR
                    (
                      (
                        0 < x
                        /\
                        x < d
                      )
                      ->
                      (
                        abs
                        `
                        (
                          ( ( P19A6Deriv F ) ` x )
                          -
                          0
                        )
                      )
                      < e
                    )
                )
            )
          \/
          A. M e. RR
            E. d e. RR
              (
                0 < d
                /\
                A. x e. RR
                  (
                    (
                      0 < x
                      /\
                      x < d
                    )
                    ->
                    M < ( P19A6Envelope F r x )
                  )
              )
        )
      )
  $.
$}
