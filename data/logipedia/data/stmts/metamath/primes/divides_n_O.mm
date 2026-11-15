$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_n_O (logipedia__metamath__primes.divides_n_O), catalog title
  "primes.divides_n_O": every natural number divides zero. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n in NN0, SetMM's n || 0 is equivalent to the
  source relation primes.divides n nat.O, which holds exactly when some
  natural q satisfies 0 = n x. q. The restricted universal quantifier
  preserves the source binder and conclusion. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-primes-divides-n-O $a |-
  A. n e. NN0 n || 0
$.
