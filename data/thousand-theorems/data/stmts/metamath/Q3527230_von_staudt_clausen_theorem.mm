$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527230
  (thousand-theorems__metamath__Q3527230), "Von Staudt-Clausen theorem": for
  every natural number k, the even-indexed Bernoulli number B_(2k), augmented
  by the sum of 1/p over primes p < 2k + 2 such that p - 1 divides 2k, is an
  integer. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers. For N in NN0,
  ( N BernPoly 0 ) is the N-th Bernoulli number with B_1 = -1/2, matching the
  source convention. The half-open interval

    ( 0 ..^ ( ( 2 x. k ) + 2 ) )

  is exactly Lean's Finset.range (2 * k + 2). Inside the prime filter,
  SetMM integer subtraction agrees with the source natural subtraction because
  every prime is at least two. Membership of the resulting rational number in
  ZZ is equivalent to membership in Set.range Int.cast.

  The declaration below is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k p $.

  thousand-theorems-q3527230-von-staudt-clausen $a
    |- A. k e. NN0
         (
           (
             ( ( 2 x. k ) BernPoly 0 )
             +
             sum_ p e.
               { p e. ( 0 ..^ ( ( 2 x. k ) + 2 ) ) |
                 ( p e. Prime /\ ( p - 1 ) || ( 2 x. k ) )
               }
               ( 1 / p )
           )
           e. ZZ
         )
  $.
$}
