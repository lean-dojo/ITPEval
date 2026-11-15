$(
  Statement-only formalization of PutnamBench artifact putnam_1962_a5:
  the closed form for the sum from k = 1 through n of the binomial
  coefficient n choose k times k squared. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The included set.mm library supplies nonnegative integers, inclusive
  integer intervals, binomial coefficients, natural powers, products, and
  finite sums. The final unproved $a assertion states the source equality
  directly for every natural n at least two.
$)

${
  $d k n $.

  putnambench-putnam-1962-a5 $a |- A. n e. NN0
    (
      2 <_ n
      ->
      (
        ( ( n x. ( n + 1 ) ) x. ( 2 ^ ( n - 2 ) ) )
        =
        sum_ k e. ( 1 ... n )
          ( ( n _C k ) x. ( k ^ 2 ) )
      )
    )
  $.
$}
