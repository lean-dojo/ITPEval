$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.gcd_O_to_eq_O (logipedia__metamath__gcd.gcd_O_to_eq_O), catalog title
  "gcd.gcd_O_to_eq_O": if the greatest common divisor of two natural numbers
  is zero, then both numbers are zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and therefore represents the
  source natural-number domain. The infix gcd operation is SetMM's standard
  greatest common divisor on that domain, while native equality, implication,
  and conjunction represent the corresponding source connectives. The final
  declaration is the single unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-gcd-gcd-o-to-eq-o $a |-
    A. m e. NN0 A. n e. NN0
      (
        ( ( m gcd n ) = 0 )
        ->
        ( ( m = 0 ) /\ ( n = 0 ) )
      )
  $.
$}
