$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.prime_to_gcd_1 (logipedia__metamath__gcd.prime_to_gcd_1), catalog title
  "gcd.prime_to_gcd_1": if a natural number n is prime and does not divide a
  natural number m, then their greatest common divisor is one. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents both source
  natural-number domains. On NN0, Prime is the class of natural prime
  numbers, integer divisibility is equivalent to the source existential
  natural-multiplier definition of primes.divides, and SetMM's infix gcd is
  the source natural greatest common divisor. Native negation and equality
  represent connectives.Not and logic.eq. The two restricted universal
  quantifiers and nested implications preserve the source scopes exactly.
  The final declaration is the single unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-gcd-prime-to-gcd-1 $a |-
    A. n e. NN0 A. m e. NN0
      (
        n e. Prime
        ->
        (
          -. n || m
          ->
          ( n gcd m ) = 1
        )
      )
  $.
$}
