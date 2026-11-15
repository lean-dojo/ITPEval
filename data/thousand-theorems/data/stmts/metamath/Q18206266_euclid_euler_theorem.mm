$(
  Statement-only formalization of Thousand Theorems corpus artifact Q18206266
  (thousand-theorems__metamath__Q18206266), "Euclid-Euler theorem": every
  natural number that is even and perfect is a power of two times a prime
  Mersenne number of the corresponding exponent. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and NN are SetMM's classes of nonnegative and positive integers.
  Divisibility by 2 states evenness, while positivity together with
  ( 1 sigma n ) = ( 2 x. n ) states Nat.Perfect n via the full sum of
  positive divisors.

  The witness k remains existentially quantified over all natural numbers.
  The associated Mersenne number ( 2 ^ ( k + 1 ) ) - 1 is required to lie in
  SetMM's standard Prime class, and the displayed equality is exactly the
  source factorization. The final declaration is the single unproved $a
  corpus statement; this file contains no $p proof statement.
$)

${
  $d k n $.

  thousand-theorems-q18206266-euclid-euler-theorem $a
    |- A. n e. NN0
         (
           (
             (
               n e. NN
               /\
               2 || n
             )
             /\
             ( ( 1 sigma n ) = ( 2 x. n ) )
           )
           ->
           E. k e. NN0
             (
               ( ( ( 2 ^ ( k + 1 ) ) - 1 ) e. Prime )
               /\
               n =
                 ( ( 2 ^ k ) x. ( ( 2 ^ ( k + 1 ) ) - 1 ) )
             )
         )
  $.
$}
