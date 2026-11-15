$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_b1: evaluation of a normalized finite sum of differences of
  integer floors as the real limit log 4 minus 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The sequence is indexed by NN0, matching the natural-number index in both
  ground-truth sources. For each n, ( 1 ... n ) is the inclusive integer
  interval from 1 through n, and |_ is SetMM's floor function on the reals.
  Thus the summand and normalization are exactly the source expressions after
  the standard coercions of natural and integer values into RR.

  The limit is the annotated solution (4,1), namely ( log 4 ) - 1. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d k n $.

  putnambench-putnam-1976-b1 $a |-
    (
      n e. NN0 |->
        (
          ( 1 / n )
          x.
          sum_ k e. ( 1 ... n )
            (
              ( |_ ` ( ( 2 x. n ) / k ) )
              -
              ( 2 x. ( |_ ` ( n / k ) ) )
            )
        )
    )
    ~~>
    ( ( log ` 4 ) - 1 )
  $.
$}
