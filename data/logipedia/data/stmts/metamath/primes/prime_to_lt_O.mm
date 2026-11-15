$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.prime_to_lt_O (logipedia__metamath__primes.prime_to_lt_O), catalog
  title "primes.prime_to_lt_O": every prime natural number is strictly
  greater than zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, membership in Prime is equivalent to the
  source definition primes.prime: the number is greater than one and every
  divisor greater than one equals the number. SetMM's native strict order
  represents nat.lt, with 0 representing nat.O. The restricted universal
  quantifier and implication preserve the source binder, hypothesis, and
  conclusion exactly. The final declaration is Metamath's native unproved $a
  statement encoding; no $p proof is supplied for this artifact.
$)

logipedia-primes-prime-to-lt-O $a |-
  A. p e. NN0
    (
      p e. Prime
      ->
      0 < p
    )
$.
