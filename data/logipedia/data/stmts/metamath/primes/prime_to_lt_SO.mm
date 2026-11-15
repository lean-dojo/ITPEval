$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.prime_to_lt_SO (logipedia__metamath__primes.prime_to_lt_SO),
  catalog title "primes.prime_to_lt_SO": every natural prime is strictly
  greater than one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 preserves the source natural-number domain. The source prime predicate,
  which says that the number is greater than one and has no divisor strictly
  between one and itself, is equivalent over naturals to SetMM's Prime class.
  The restricted universal quantifier and implication preserve the source
  scope exactly. The final declaration is an unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

logipedia-primes-prime-to-lt-SO $a |-
  A. p e. NN0 ( p e. Prime -> 1 < p )
$.
