$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_a4: convergence of the alternating real series with terms
  n to the power negative n to the integral of x to the power x on the
  unit interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The mapping on ZZ is the integer-indexed sequence from the Isabelle and
  Lean sources. For each n its finite sum uses the inclusive positive-integer
  interval 1 ... n; values before index one do not affect the limit and its
  restriction to natural indices is the Rocq sequence.

  Since every summation index i is positive, division by i ^ i is exactly
  multiplication by i raised to negative i. On the open interval (0,1),
  exp(x * log(x)) is x raised to the real power x. The open-interval
  Lebesgue integral matches the Lean and Rocq sources, and endpoint inclusion
  does not change it, matching the Isabelle interval integral.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n x $.

  putnambench-putnam-1969-a4 $a |-
    (
      n e. ZZ |->
        sum_ i e. ( 1 ... n )
          (
            ( ( -u 1 ) ^ ( i + 1 ) )
            /
            ( i ^ i )
          )
    )
    ~~>
    (
      S. ( 0 (,) 1 )
        ( exp ` ( x x. ( log ` x ) ) )
        _d x
    )
  $.
$}
