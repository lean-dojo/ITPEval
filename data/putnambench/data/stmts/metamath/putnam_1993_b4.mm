$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_b4: positive continuous real functions and a positive
  continuous kernel on the unit square satisfying reciprocal integral
  equations agree throughout the unit interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K ranges over all real-valued functions on RR X. RR, while f and g range
  over all total real-valued functions on RR. Joint continuity of K on the
  unit square is expanded in relative epsilon-delta form; coordinatewise
  delta neighborhoods induce the standard product topology. Continuity of f
  and g is asserted for their restrictions to [0,1].

  Set.mm's S. binder is the real Lebesgue integral. Endpoint inclusion does
  not affect these integrals, so the closed interval notation agrees with the
  open-interval and interval-integral formulations in the ground truths.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d K d e f g u v x y $.

  putnambench-putnam-1993-b4 $a |-
    A. K e. ( RR ^m ( RR X. RR ) )
    A. f e. ( RR ^m RR )
    A. g e. ( RR ^m RR )
      (
        (
          A. x e. ( 0 [,] 1 ) A. y e. ( 0 [,] 1 )
            0 < ( K ` <. x , y >. )
          /\
          (
            A. x e. ( 0 [,] 1 ) A. y e. ( 0 [,] 1 ) A. e e. RR
              (
                0 < e
                ->
                E. d e. RR
                  (
                    0 < d
                    /\
                    A. u e. ( 0 [,] 1 ) A. v e. ( 0 [,] 1 )
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
                            ( K ` <. u , v >. )
                            -
                            ( K ` <. x , y >. )
                          )
                        )
                        < e
                      )
                  )
              )
            /\
            (
              A. x e. ( 0 [,] 1 )
                (
                  0 < ( f ` x )
                  /\
                  0 < ( g ` x )
                )
              /\
              (
                (
                  ( f |` ( 0 [,] 1 ) )
                  e. ( ( 0 [,] 1 ) -cn-> RR )
                  /\
                  ( g |` ( 0 [,] 1 ) )
                  e. ( ( 0 [,] 1 ) -cn-> RR )
                )
                /\
                A. x e. ( 0 [,] 1 )
                  (
                    (
                      S. ( 0 [,] 1 )
                        (
                          ( f ` y )
                          x.
                          ( K ` <. x , y >. )
                        )
                        _d y
                    )
                    =
                    ( g ` x )
                    /\
                    (
                      S. ( 0 [,] 1 )
                        (
                          ( g ` y )
                          x.
                          ( K ` <. x , y >. )
                        )
                        _d y
                    )
                    =
                    ( f ` x )
                  )
              )
            )
          )
        )
        ->
        A. x e. ( 0 [,] 1 )
          ( f ` x ) = ( g ` x )
      )
  $.
$}
