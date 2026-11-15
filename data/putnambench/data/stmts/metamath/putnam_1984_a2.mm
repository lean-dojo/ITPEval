$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_a2: evaluation as 2 of an infinite rational series whose
  terms involve powers of 6, 3, and 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the finite sum is the partial sum from k = 1 through n
  of the series in the Lean and Isabelle sources. Its terms are rational
  numbers, and viewing those partial sums in RR preserves their ordinary
  rational-series convergence and value.

  The Rocq source instead starts at k = 0, where its totalized real division
  makes the term zero because the second denominator factor is 1 - 1.
  Removing that zero term gives exactly the same sequence of partial sums.
  The value 2 is explicit in Rocq and in the Lean and Isabelle solution
  annotations. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d k n $.

  putnambench-putnam-1984-a2 $a |-
    (
      n e. NN |->
        sum_ k e. ( 1 ... n )
          (
            ( 6 ^ k )
            /
            (
              (
                ( 3 ^ ( k + 1 ) )
                -
                ( 2 ^ ( k + 1 ) )
              )
              x.
              (
                ( 3 ^ k )
                -
                ( 2 ^ k )
              )
            )
          )
    )
    ~~>
    2
  $.
$}
