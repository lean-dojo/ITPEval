$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_a5: divisibility by the square of a prime of a partial sum
  of binomial coefficients ending at the floor of two thirds of the prime.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime and NN0 are set.mm's classes of natural primes and nonnegative
  integers. The equality defining k uses the real floor function, matching
  floor(2p/3) in all ground-truth sources. The interval 1 ... k is inclusive,
  _C is the binomial coefficient operation, sum_ is finite summation, and ||
  is integer divisibility.

  Restricting p to Prime is logically equivalent to the source's natural p
  together with its primality hypothesis. The explicit natural k and its
  defining equality preserve the source binder and assumption. The final
  declaration is the single unproved $a corpus statement. This artifact file
  declares no $p statement; the included set.mm supplies the proved library.
$)

${
  $d i k p $.

  putnambench-putnam-1996-a5 $a |-
    A. p e. Prime
      A. k e. NN0
        (
          (
            3 < p
            /\
            k = ( |_ ` ( ( 2 x. p ) / 3 ) )
          )
          ->
          (
            ( p ^ 2 )
            ||
            sum_ i e. ( 1 ... k ) ( p _C i )
          )
        )
  $.
$}
