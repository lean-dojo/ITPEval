$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_a4: evaluation as 9 / 32 of an iterated real series over two
  positive-integer indices. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the class of nonnegative integers. The successor shifts
  m + 1 and n + 1 therefore give exactly the positive indices in the
  displayed Putnam series.

  The two unbounded sum_ binders are SetMM's convergent infinite real-series
  sums. Their nesting preserves the source order: for each m, first sum over
  n, and then sum those values over m. The summand and its denominator are
  transcribed directly, and the right side is the explicit Rocq solution and
  the value annotated in the Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d m n $.

  putnambench-putnam-1999-a4 $a |-
    (
      sum_ m e. NN0
        (
          sum_ n e. NN0
            (
              (
                ( ( m + 1 ) ^ 2 )
                x.
                ( n + 1 )
              )
              /
              (
                ( 3 ^ ( m + 1 ) )
                x.
                (
                  (
                    ( n + 1 )
                    x.
                    ( 3 ^ ( m + 1 ) )
                  )
                  +
                  (
                    ( m + 1 )
                    x.
                    ( 3 ^ ( n + 1 ) )
                  )
                )
              )
            )
        )
    )
    =
    ( 9 / ( 2 ^ 5 ) )
  $.
$}
