$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_n_n (logipedia__metamath__primes.divides_n_n), catalog title
  "primes.divides_n_n": every natural number divides itself. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n in NN0, SetMM's n || n is equivalent to the
  source relation primes.divides n n, whose multiplier characterization is
  that some natural q satisfies n = n x. q. The restricted universal
  quantifier preserves the source binder and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-primes-divides-n-n $a |-
  A. n e. NN0 n || n
$.
