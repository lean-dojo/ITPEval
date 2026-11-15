$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_b4: evaluation of a real infinite series involving natural
  logarithms at four consecutive linear arguments. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the class of nonnegative integers, so the sum_ binder
  preserves the source index k >= 0. Each logarithm is evaluated at a
  positive integer, where SetMM's log agrees with the real natural logarithm,
  and the unbounded sum is SetMM's convergent infinite-series sum.

  The denominator of the third term is 4k + 4, as in the published problem
  and the Lean and Rocq statements; the Isabelle source's 4k - 4 is an
  evident transcription error. The right side is the published value
  (log 2)^2 recorded by the Lean and Isabelle solution annotations. The Rocq
  definition instead squares log(2) / log(10), which conflicts with its own
  use of the natural logarithm in the series.

  The declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

putnambench-putnam-2017-b4 $a |-
    (
      sum_ k e. NN0
        (
          (
            (
              3
              x.
              ( log ` ( ( 4 x. k ) + 2 ) )
            )
            /
            ( ( 4 x. k ) + 2 )
          )
          -
          (
            ( log ` ( ( 4 x. k ) + 3 ) )
            /
            ( ( 4 x. k ) + 3 )
          )
          -
          (
            ( log ` ( ( 4 x. k ) + 4 ) )
            /
            ( ( 4 x. k ) + 4 )
          )
          -
          (
            ( log ` ( ( 4 x. k ) + 5 ) )
            /
            ( ( 4 x. k ) + 5 )
          )
        )
    )
    =
    ( ( log ` 2 ) ^ 2 )
  $.
