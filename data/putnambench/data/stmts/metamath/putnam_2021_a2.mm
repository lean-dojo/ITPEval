$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_a2: evaluation as exp(1) of the positive-infinity limit of
  g(x)/x, where g(x) is defined by the stated right-hand real-power limit
  at zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function g ranges over all total real-valued functions. For every
  positive real x, the antecedent expands the right-hand limit at zero into
  its epsilon-delta definition, keeping epsilon, delta, and the approaching
  variable r internally quantified.

  When x > 0 and r > 0, x + 1 and x are positive, r + 1 is positive, and
  (x+1)^(r+1) - x^(r+1) is positive. Hence set.mm's complex-power operation
  ^c is real-valued and agrees with the source real-power operation at every
  point used by the one-sided limit. The relation ~~>r is set.mm's finite
  real limit at positive infinity, so the conclusion directly states that
  g(x)/x tends to exp(1).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d d e g r x $.

  putnambench-putnam-2021-a2 $a |-
    A. g e. ( RR ^m RR )
      (
        (
          A. x e. RR
            (
              0 < x
              ->
              A. e e. RR
                (
                  0 < e
                  ->
                  E. d e. RR
                    (
                      0 < d
                      /\
                      A. r e. RR
                        (
                          (
                            0 < r
                            /\
                            r < d
                          )
                          ->
                          (
                            abs
                            `
                            (
                              (
                                (
                                  (
                                    ( x + 1 )
                                    ^c
                                    ( r + 1 )
                                  )
                                  -
                                  ( x ^c ( r + 1 ) )
                                )
                                ^c
                                ( 1 / r )
                              )
                              -
                              ( g ` x )
                            )
                          )
                          < e
                        )
                    )
                )
            )
        )
        ->
        (
          x e. RR |->
            ( ( g ` x ) / x )
        )
        ~~>r
        ( exp ` 1 )
      )
  $.
$}
