$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.commutative_gcd (logipedia__metamath__gcd.commutative_gcd), catalog
  title "gcd.commutative_gcd": the greatest common divisor of any two natural
  numbers is unchanged when its arguments are exchanged. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and therefore represents the
  source natural-number domain. The infix gcd operation is SetMM's standard
  greatest common divisor, and native equality represents the source
  natural-number equality. The final declaration is the single unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d m n $.

  logipedia-gcd-commutative-gcd $a
    |- A. n e. NN0 A. m e. NN0
         ( n gcd m ) = ( m gcd n )
  $.
$}
