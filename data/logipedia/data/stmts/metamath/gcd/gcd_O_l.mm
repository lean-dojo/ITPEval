$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.gcd_O_l (logipedia__metamath__gcd.gcd_O_l), catalog title
  "gcd.gcd_O_l": the greatest common divisor of zero and any natural number
  is that natural number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and therefore represents the
  source natural-number domain. The infix gcd operation is SetMM's standard
  greatest common divisor on that domain, and native equality represents the
  source natural-number equality. The final declaration is the single
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-gcd-gcd-o-l $a |-
  A. m e. NN0 ( ( 0 gcd m ) = m )
$.
