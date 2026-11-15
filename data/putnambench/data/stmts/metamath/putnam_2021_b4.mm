$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_b4: the remainder modulo a Fibonacci number of the product
  of k^k for positive k below that number is itself a Fibonacci number.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total NN0-valued sequences indexed by NN0. The two
  initial values and the recurrence at every nonnegative index are exactly
  the Fibonacci hypotheses in the source statements. For each m > 2, the
  product range 1 ... (F(m) - 1) is the inclusive source range, and p remains
  internally existentially quantified.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d F k m n p $.

  putnambench-putnam-2021-b4 $a |-
    A. F e. ( NN0 ^m NN0 )
      (
        (
          (
            ( F ` 0 ) = 0
            /\
            ( F ` 1 ) = 1
          )
          /\
          A. n e. NN0
            (
              ( F ` ( n + 2 ) )
              =
              (
                ( F ` ( n + 1 ) )
                +
                ( F ` n )
              )
            )
        )
        ->
        A. m e. NN0
          (
            2 < m
            ->
            E. p e. NN0
              (
                (
                  prod_ k e. ( 1 ... ( ( F ` m ) - 1 ) )
                    ( k ^ k )
                )
                mod
                ( F ` m )
              )
              =
              ( F ` p )
          )
      )
  $.
$}
