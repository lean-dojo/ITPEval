$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_a4: for every positive natural number n, the number
  10^(10^(10^n)) + 10^(10^n) + 10^n - 1 is not prime. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive natural numbers, and Prime is its
  class of natural primes. Thus the bounded universal quantifier is
  equivalent to quantifying over all natural n under the assumption n > 0.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  putnambench-putnam-2010-a4 $a |- A. n e. NN
    -.
    (
      (
        (
          (
            ( ; 1 0 )
            ^
            (
              ( ; 1 0 )
              ^
              ( ( ; 1 0 ) ^ n )
            )
          )
          +
          (
            ( ; 1 0 )
            ^
            ( ( ; 1 0 ) ^ n )
          )
        )
        +
        ( ( ; 1 0 ) ^ n )
      )
      -
      1
    )
    e.
    Prime
  $.
$}
