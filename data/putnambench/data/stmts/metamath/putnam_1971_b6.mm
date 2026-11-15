$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_b6: the partial sums of the greatest-odd-divisor ratio
  differ from two thirds of the positive integer endpoint by less than
  one in absolute value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function d is quantified on the positive integers, exactly the
  inputs used by the source theorem. The antecedent says that d(n) is an
  odd divisor of n and is at least every odd divisor of n. Oddness and
  divisibility are rendered by internally existential natural-number
  witnesses, so this is equivalent to d(n) being the greatest odd divisor.
  The finite sum and all divisions are evaluated in SetMM's real/complex
  arithmetic, agreeing with the source coercions to real or rational values.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d d i k n q t x $.

  putnambench-putnam-1971-b6 $a |-
    A. d e. ( NN ^m NN )
      (
        (
          A. n e. NN
            (
              (
                E. k e. NN0
                  ( d ` n ) = ( ( 2 x. k ) + 1 )
                /\
                E. q e. NN
                  n = ( ( d ` n ) x. q )
              )
              /\
              A. t e. NN
                (
                  (
                    (
                      E. k e. NN0
                        t = ( ( 2 x. k ) + 1 )
                      /\
                      E. q e. NN
                        n = ( t x. q )
                    )
                    ->
                    t <_ ( d ` n )
                  )
                )
            )
          ->
          A. x e. NN
            (
              (
                abs
                `
                (
                  (
                    sum_ i e. ( 1 ... x )
                      ( ( d ` i ) / i )
                  )
                  -
                  ( ( 2 x. x ) / 3 )
                )
              )
              <
              1
            )
        )
      )
  $.
$}
