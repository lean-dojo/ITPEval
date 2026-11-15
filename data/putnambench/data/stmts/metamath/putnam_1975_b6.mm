$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_b6: two strict inequalities comparing harmonic partial sums
  with real powers of consecutive positive integers. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, and ( 1 ... n ) is the
  inclusive integer interval from one through n. Thus the finite sum in each
  conjunct is exactly s_n = 1 + 1/2 + ... + 1/n.

  Under the displayed hypotheses, the bases n + 1 and n are positive.
  Consequently set.mm's complex-power operation ^c agrees with the source
  real power exp(exponent * log(base)). The source function s is inlined by
  its defining harmonic-sum expression, a definitional equivalence.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n $.

  putnambench-putnam-1975-b6 $a |- (
    A. n e. NN0
      (
        1 < n
        ->
        (
          n
          x.
          (
            ( n + 1 )
            ^c
            ( 1 / n )
          )
        )
        <
        (
          n
          +
          sum_ i e. ( 1 ... n )
            ( 1 / i )
        )
      )
    /\
    A. n e. NN0
      (
        2 < n
        ->
        (
          ( n - 1 )
          x.
          (
            n
            ^c
            (
              ( -u 1 )
              /
              ( n - 1 )
            )
          )
        )
        <
        (
          n
          -
          sum_ i e. ( 1 ... n )
            ( 1 / i )
        )
      )
  ) $.
$}
