$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_b5: for every positive integer n, the sum of the first n
  terms of the binomial expansion of (2 - 1) raised to the power -n,
  starting with the largest power of 2, equals one half. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The half-open integer interval ( 0 ..^ n ) is the source range from zero
  through n - 1. For each index i in this range, division by
  2 ^ ( n + i ) is equivalent to multiplication by the source negative
  integer power 2 ^ ( -n - i ). The final declaration is the single
  unproved $a corpus statement.
$)

${
  $d i n $.

  putnambench-putnam-1967-b5 $a |-
    A. n e. NN
      (
        ( 1 / 2 )
        =
        sum_ i e. ( 0 ..^ n )
          (
            (
              ( ( n + i ) - 1 )
              _C
              i
            )
            /
            ( 2 ^ ( n + i ) )
          )
      )
  $.
$}
