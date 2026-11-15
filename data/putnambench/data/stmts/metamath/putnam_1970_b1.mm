$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_b1: evaluation of a real infinite-product limit as an
  exponential involving the natural logarithm and arctangent. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The sequence is indexed by the positive integers. This is the tail from
  index one of the natural- or integer-indexed sequences in the sources, so
  it has exactly the same limit at infinity while avoiding the irrelevant
  initial expression containing 1 / 0.

  For every positive n, the finite product is over the inclusive interval
  from 1 through 2n. Since n^2 + i^2 is positive on this interval, set.mm's
  complex-power operation ^c agrees with the source real power
  exp((1 / n) log(n^2 + i^2)). The right side is the explicit solution from
  the Rocq source and the solution annotations in the Lean and Isabelle
  sources. The final declaration is an unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n $.

  putnambench-putnam-1970-b1 $a |-
    (
      n e. NN |->
        (
          ( 1 / ( n ^ 4 ) )
          x.
          prod_ i e. ( 1 ... ( 2 x. n ) )
            (
              ( ( n ^ 2 ) + ( i ^ 2 ) )
              ^c
              ( 1 / n )
            )
        )
    )
    ~~>
    (
      exp
      `
      (
        (
          ( 2 x. ( log ` 5 ) )
          -
          4
        )
        +
        ( 2 x. ( arctan ` 2 ) )
      )
    )
  $.
$}
