$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_a6: an integral inequality for a continuous real-valued
  function on the unit square, comparing squared marginal integrals with
  the squared total integral and the integral of the squared function.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all real-valued functions whose domain is exactly
  ( 0 [,] 1 ) X. ( 0 [,] 1 ). The antecedent is relative epsilon-delta
  continuity on that square; coordinatewise delta neighborhoods induce its
  standard product topology.

  Set.mm's S. binder is the real Lebesgue integral. The first two terms are
  the squared x- and y-marginal integrals, while the right side is the square
  of the iterated total integral plus the iterated integral of F squared.
  These iterated integrals equal the corresponding square integrals for
  continuous F. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d F d e u v x y $.

  putnambench-putnam-2004-a6 $a |-
    A. F e.
      ( RR ^m ( ( 0 [,] 1 ) X. ( 0 [,] 1 ) ) )
      (
        (
          A. x e. ( 0 [,] 1 )
          A. y e. ( 0 [,] 1 )
          A. e e. RR
            (
              0 < e
              ->
              E. d e. RR
                (
                  0 < d
                  /\
                  A. u e. ( 0 [,] 1 )
                  A. v e. ( 0 [,] 1 )
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
        ->
        (
          (
            S. ( 0 [,] 1 )
              (
                (
                  S. ( 0 [,] 1 )
                    ( F ` <. x , y >. )
                    _d x
                )
                ^ 2
              )
              _d y
            +
            S. ( 0 [,] 1 )
              (
                (
                  S. ( 0 [,] 1 )
                    ( F ` <. x , y >. )
                    _d y
                )
                ^ 2
              )
              _d x
          )
          <_
          (
            (
              S. ( 0 [,] 1 )
                (
                  S. ( 0 [,] 1 )
                    ( F ` <. x , y >. )
                    _d x
                )
                _d y
            )
            ^ 2
            +
            S. ( 0 [,] 1 )
              (
                S. ( 0 [,] 1 )
                  ( ( F ` <. x , y >. ) ^ 2 )
                  _d x
              )
              _d y
          )
        )
      )
  $.
$}
