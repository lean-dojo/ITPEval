$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_b2: evaluation of a punctured real limit at zero involving
  real powers of an interval integral between two positive real parameters.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For 0 < a < b and x in [0,1], the base b*x + a*(1-x) is positive.
  Consequently set.mm's complex-power operation ^c agrees here with the
  source real-power operation, both inside the Lebesgue integral and for
  the positive value of that integral.

  The nested epsilon-delta quantifiers are the punctured two-sided limit as
  t tends to zero. The displayed value is

    exp(-1) * (b^b / a^a)^(1/(b-a)),

  which is algebraically identical to the explicit Rocq solution
  exp((b/(b-a))*log b) / (exp(1)*exp((a/(b-a))*log a)).
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b d e t x $.

  putnambench-putnam-1979-b2 $a |- A. a e. RR A. b e. RR
    (
      (
        0 < a
        /\
        a < b
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
              A. t e. RR
                (
                  (
                    0 < ( abs ` t )
                    /\
                    ( abs ` t ) < d
                  )
                  ->
                  (
                    abs
                    `
                    (
                      (
                        S. ( 0 [,] 1 )
                        (
                          (
                            ( b x. x )
                            +
                            ( a x. ( 1 - x ) )
                          )
                          ^c
                          t
                        )
                        _d x
                        ^c
                        ( 1 / t )
                      )
                      -
                      (
                        ( exp ` ( -u 1 ) )
                        x.
                        (
                          (
                            ( b ^c b )
                            /
                            ( a ^c a )
                          )
                          ^c
                          ( 1 / ( b - a ) )
                        )
                      )
                    )
                  )
                  < e
                )
            )
        )
    )
  $.
$}
