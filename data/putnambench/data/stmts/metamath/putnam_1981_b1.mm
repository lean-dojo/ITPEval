$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_b1: the normalized double sum of
  5 h^4 - 18 h^2 k^2 + 5 k^4 over 1 <= h,k <= n converges to -1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The NN0-indexed mapping uses set.mm's real arithmetic, inclusive finite
  integer ranges, finite sums, and sequence-limit relation directly. Its
  value at n = 0 does not affect convergence. The target -1 is the explicit
  solution in the Rocq source and the solution annotation in the Lean and
  Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d h k n $.

  putnambench-putnam-1981-b1 $a |-
    (
      n e. NN0 |->
        (
          ( 1 / ( n ^ 5 ) )
          x.
          sum_ h e. ( 1 ... n )
            sum_ k e. ( 1 ... n )
              (
                (
                  ( 5 x. ( h ^ 4 ) )
                  -
                  ( ( ( 9 + 9 ) x. ( h ^ 2 ) ) x. ( k ^ 2 ) )
                )
                +
                ( 5 x. ( k ^ 4 ) )
              )
        )
    )
    ~~>
    ( -u 1 )
  $.
$}
