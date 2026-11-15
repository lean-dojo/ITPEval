$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_b5: for every nonnegative integer n, the finite real
  exponential-series sum from i = 0 through n of n^i / i! is greater than
  exp(n) / 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the set of nonnegative integers, and ( 0 ... n ) is the inclusive
  integer interval from zero through n. The summand uses set.mm's natural
  exponentiation and factorial, interpreted in the real division expression.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n $.

  putnambench-putnam-1974-b5 $a |- A. n e. NN0
    (
      ( ( exp ` n ) / 2 )
      <
      sum_ i e. ( 0 ... n )
        (
          ( n ^ i )
          /
          ( ! ` i )
        )
    )
  $.
$}
