$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_a2: convergence of the series built from B_n(log base n of 2),
  normalized by the square of n log base 2 of n. This file has no proof.
$)

$[ lib/set.mm $]

$(
  For each partial-sum bound N, the outer sum begins at n = 2. The inner
  finite sum is B_n(log_n 2) over k = 1 through n. SetMM's ^c is real
  exponentiation on these positive bases, logb is the generalized logarithm,
  and ~~> is the standard real-sequence convergence relation.

  The denominator is (n log_2 n)^2, as in the published problem, Lean, and
  Isabelle. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d N k n $.

  putnambench-putnam-1982-a2 $a |-
    E. L e. RR
      (
        N e. NN0 |->
          sum_ n e. ( 2 ... N )
            (
              (
                sum_ k e. ( 1 ... n )
                  ( k ^c ( n logb 2 ) )
              )
              /
              (
                (
                  n
                  x.
                  ( 2 logb n )
                )
                ^
                2
              )
            )
      )
      ~~>
      L
  $.
$}
