$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1186808
  (thousand-theorems__metamath__Q1186808), "Lucas's theorem": for a prime p
  and bounded nonnegative integers n and k, the binomial coefficient n choose
  k is congruent modulo p to the product of the binomial coefficients of
  corresponding base-p digits. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime and NN0 are SetMM's classes of natural primes and nonnegative
  integers. The half-open interval 0 ..^ a is Lean's range a. For each index
  i, floor division by p ^ i followed by remainder modulo p extracts the
  corresponding base-p digit. The finite product is therefore the product in
  Choose.lucas_theorem.

  Since p is positive, equality of the displayed remainders is equivalent to
  the source integer congruence modulo p. The final declaration is the single
  unproved $a corpus statement; this candidate root file adds no $p statement.
$)

${
  $d a i k n p $.

  thousand-theorems-q1186808-lucas $a |-
    A. p e. Prime
      A. n e. NN0
        A. k e. NN0
          A. a e. NN0
            (
              (
                n < ( p ^ a )
                /\
                k < ( p ^ a )
              )
              ->
              (
                ( ( n _C k ) mod p )
                =
                (
                  (
                    prod_ i e. ( 0 ..^ a )
                      (
                        (
                          ( |_ ` ( n / ( p ^ i ) ) ) mod p
                        )
                        _C
                        (
                          ( |_ ` ( k / ( p ^ i ) ) ) mod p
                        )
                      )
                  )
                  mod p
                )
              )
            )
  $.
$}
