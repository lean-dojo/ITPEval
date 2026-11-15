$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.decidable_divides
  (logipedia__metamath__primes.decidable_divides), catalog title
  "primes.decidable_divides": divisibility is decidable for every pair of
  natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For nonnegative n and m, SetMM's n || m is equivalent
  to the source definition that some natural q satisfies m = n x. q. The
  disjunction of divisibility with its negation exactly unfolds the source
  definition logic.decidable P := P or not P. The two restricted universal
  quantifiers preserve the source binder order and scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-primes-decidable-divides $a |-
  A. n e. NN0
    A. m e. NN0
      ( n || m \/ -. n || m )
$.
