$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_le (logipedia__metamath__primes.divides_to_le), catalog
  title "primes.divides_to_le": a natural divisor of a positive natural
  number is less than or equal to that number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For n and m in NN0, SetMM's n || m is equivalent to
  the source relation primes.divides n m, characterized by a natural
  multiplier q satisfying m = n x. q. SetMM's native strict and non-strict
  orders represent nat.lt and nat.le. The restricted universal quantifiers
  and nested implications preserve the source binder order, assumptions,
  conclusion, and all scopes. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d m n $.

  logipedia-primes-divides-to-le $a |-
    A. n e. NN0
      A. m e. NN0
        (
          0 < m
          ->
          (
            n || m
            ->
            n <_ m
          )
        )
  $.
$}
