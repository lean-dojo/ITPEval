$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_b1: no three consecutive coefficients vanish in a real power
  series locally equal to the factorial-weighted series
  sum_n x^n (x-1)^(2n) / n!. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is the class of all real-valued sequences indexed by the
  nonnegative integers. The two sum_ expressions are set.mm's unbounded
  real-series sums. Eliminating the source's definitionally specified
  auxiliary function S gives the displayed local equality directly.

  The positive real a and the coefficient index n remain internally
  existentially quantified. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a n p x $.

  putnambench-putnam-1972-b1 $a |- A. p e. ( RR ^m NN0 )
    (
      (
        E. a e. RR+
          A. x e. RR
            (
              ( ( abs ` x ) < a )
              ->
              (
                sum_ n e. NN0
                  (
                    ( p ` n )
                    x.
                    ( x ^ n )
                  )
              )
              =
              (
                sum_ n e. NN0
                  (
                    (
                      ( x ^ n )
                      x.
                      ( ( x - 1 ) ^ ( 2 x. n ) )
                    )
                    /
                    ( ! ` n )
                  )
              )
            )
      )
      ->
      -.
      E. n e. NN0
        (
          ( p ` n ) = 0
          /\
          (
            ( p ` ( n + 1 ) ) = 0
            /\
            ( p ` ( n + 2 ) ) = 0
          )
        )
    )
  $.
$}
