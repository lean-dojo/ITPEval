$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.divides_gcd_l (logipedia__metamath__gcd.divides_gcd_l), catalog title
  "gcd.divides_gcd_l": the greatest common divisor of any two natural
  numbers divides the first number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's gcd is the natural greatest common
  divisor, and integer divisibility is equivalent to the source existential
  natural-multiplier definition of primes.divides. The two restricted
  universal quantifiers and divisibility conclusion preserve the source
  statement exactly. The final declaration is the single unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-gcd-divides-gcd-l $a |-
    A. n e. NN0 A. m e. NN0
      ( n gcd m ) || n
  $.
$}
