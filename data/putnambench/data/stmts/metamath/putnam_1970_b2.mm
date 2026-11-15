$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_b2: the two-point average formula for the mean value of a
  real polynomial of degree at most three on a symmetric interval.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The four universally quantified real coefficients represent exactly all
  real polynomials of degree at most three. The Lebesgue integral is over
  the closed interval [-T,T]; for positive T its normalization by 2*T is
  the source average integral. The two evaluations are at -T/sqrt(3) and
  T/sqrt(3), exactly as in the ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d T a b c d x $.

  putnambench-putnam-1970-b2 $a |-
    A. T e. RR
      A. a e. RR
        A. b e. RR
          A. c e. RR
            A. d e. RR
              (
                0 < T
                ->
                (
                  (
                    (
                      (
                        (
                          a
                          x.
                          (
                            (
                              ( -u T )
                              /
                              ( sqrt ` 3 )
                            )
                            ^ 3
                          )
                        )
                        +
                        (
                          b
                          x.
                          (
                            (
                              ( -u T )
                              /
                              ( sqrt ` 3 )
                            )
                            ^ 2
                          )
                        )
                      )
                      +
                      (
                        c
                        x.
                        (
                          ( -u T )
                          /
                          ( sqrt ` 3 )
                        )
                      )
                    )
                    +
                    d
                  )
                  +
                  (
                    (
                      (
                        (
                          a
                          x.
                          (
                            (
                              T
                              /
                              ( sqrt ` 3 )
                            )
                            ^ 3
                          )
                        )
                        +
                        (
                          b
                          x.
                          (
                            (
                              T
                              /
                              ( sqrt ` 3 )
                            )
                            ^ 2
                          )
                        )
                      )
                      +
                      (
                        c
                        x.
                        (
                          T
                          /
                          ( sqrt ` 3 )
                        )
                      )
                    )
                    +
                    d
                  )
                )
                /
                2
              )
              =
              (
                (
                  1
                  /
                  ( 2 x. T )
                )
                x.
                S. ( ( -u T ) [,] T )
                  (
                    (
                      (
                        ( a x. ( x ^ 3 ) )
                        +
                        ( b x. ( x ^ 2 ) )
                      )
                      +
                      ( c x. x )
                    )
                    +
                    d
                  )
                  _d x
              )
          )
  $.
$}
