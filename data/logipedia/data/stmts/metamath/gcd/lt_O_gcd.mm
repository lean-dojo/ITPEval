$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.lt_O_gcd (logipedia__metamath__gcd.lt_O_gcd), catalog title
  "gcd.lt_O_gcd": for all natural numbers m and n, if n is positive, then
  the greatest common divisor of m and n is positive. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and therefore represents the
  source natural-number domain. On NN0, SetMM's strict order and infix gcd
  operation are the source natural strict order and greatest common divisor.
  The two restricted universal quantifiers and implication preserve the
  source scope exactly. The final declaration is the single unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-gcd-lt-o-gcd $a |-
    A. m e. NN0 A. n e. NN0
      (
        0 < n
        ->
        0 < ( m gcd n )
      )
  $.
$}
