$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_b4: for every odd prime p, the sum from j = 0 through p of
  C(p,j) C(p+j,j) is congruent to 2^p + 1 modulo p^2. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Prime and Odd are SetMM's classes of natural primes and odd integers.
  The interval 0 ... p is inclusive, _C is the binomial-coefficient
  operation, and sum_ is finite summation. Equality of the two displayed
  remainders is exactly congruence modulo p^2.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d j p $.

  putnambench-putnam-1991-b4 $a |-
    A. p e. Prime
      (
        p e. Odd
        ->
        (
          (
            (
              sum_ j e. ( 0 ... p )
                ( ( p _C j ) x. ( ( p + j ) _C j ) )
            )
            mod ( p ^ 2 )
          )
          =
          ( ( ( 2 ^ p ) + 1 ) mod ( p ^ 2 ) )
        )
      )
  $.
$}
