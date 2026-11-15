$(
  Statement-only formalization of PutnamBench artifact putnam_1962_b5:
  the two-sided real bound for the sum from i = 1 through n of
  (i / n) raised to the nth power, for every integer n greater than one.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Since n is an integer greater than one, it is a positive integer, and
  natural exponentiation agrees with the real-power notation in the Lean
  and Isabelle sources on the positive terms i / n. The final declaration
  is an unproved $a statement.
$)

${
  $d i n $.

  putnambench-putnam-1962-b5 $a |- A. n e. ZZ
    (
      1 < n
      ->
      (
        (
          ( ( ( 3 x. n ) + 1 ) / ( ( 2 x. n ) + 2 ) )
          <
          sum_ i e. ( 1 ... n ) ( ( i / n ) ^ n )
        )
        /\
        (
          sum_ i e. ( 1 ... n ) ( ( i / n ) ^ n )
          <
          2
        )
      )
    )
  $.
$}
