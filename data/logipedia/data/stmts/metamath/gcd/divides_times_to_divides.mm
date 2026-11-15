$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_times_to_divides
  (logipedia__metamath__gcd.divides_times_to_divides), catalog title
  "gcd.divides_times_to_divides": if a natural number p is prime and divides
  the product of natural numbers n and m, then p divides n or p divides m.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents each source
  natural-number domain. On NN0, SetMM's multiplication is natural
  multiplication, Prime is the class of natural prime numbers, and integer
  divisibility is equivalent to the source existential natural-multiplier
  definition of primes.divides. Native disjunction represents connectives.Or.
  The three restricted universal quantifiers and two nested implications
  preserve the source scopes and assumptions exactly. The final declaration
  is the single unproved $a statement encoding; this database contains no $p
  proof declaration.
$)

${
  $d m n p $.

  logipedia-gcd-divides-times-to-divides $a |-
    A. p e. NN0 A. n e. NN0 A. m e. NN0
      (
        p e. Prime
        ->
        (
          p || ( n x. m )
          ->
          ( p || n \/ p || m )
        )
      )
  $.
$}
