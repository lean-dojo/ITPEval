$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_dividesb_true
  (logipedia__metamath__primes.divides_to_dividesb_true), catalog title
  "primes.divides_to_dividesb_true": for natural numbers n and m, if n is
  positive and divides m, then the Boolean divisibility test of n into m
  returns true. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents both source
  natural-number domains. Under the assumption 0 < n, SetMM divisibility
  n || m is equivalent to the source existential natural-multiplier
  predicate primes.divides n m. The source definition primes.dividesb n m
  tests whether the natural remainder of m modulo n equals zero; the Boolean
  carrier is {0,1}, true is 1, and if ( ( m mod n ) = 0 , 1 , 0 ) is exactly
  that Boolean test. The restricted universal quantifiers and nested
  implications preserve the source scopes. The final declaration is an
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d m n $.

  logipedia-primes-divides-to-dividesb-true $a |-
    A. n e. NN0
      A. m e. NN0
        (
          0 < n
          ->
          (
            n || m
            ->
            if ( ( m mod n ) = 0 , 1 , 0 ) = 1
          )
        )
  $.
$}
