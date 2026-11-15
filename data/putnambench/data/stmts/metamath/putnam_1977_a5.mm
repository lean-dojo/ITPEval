$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_a5: for a natural prime p and nonnegative integers m at least
  n, the binomial coefficients (p*m choose p*n) and (m choose n) are
  congruent modulo p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is the SetMM class of natural primes, NN0 is the class of
  nonnegative integers, _C is the binomial coefficient operation, and mod
  is natural-number remainder. Equality of the two displayed remainders is
  exactly the source congruence modulo p.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d m n p $.

  putnambench-putnam-1977-a5 $a |-
    A. p e. Prime A. m e. NN0 A. n e. NN0
      (
        n <_ m
        ->
        (
          ( ( ( p x. m ) _C ( p x. n ) ) mod p )
          =
          ( ( m _C n ) mod p )
        )
      )
  $.
$}
