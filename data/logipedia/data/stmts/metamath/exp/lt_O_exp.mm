$(
  Statement-only formalization of the Logipedia corpus artifact
  exp.lt_O_exp (logipedia__metamath__exp.lt_O_exp), catalog title
  "exp.lt_O_exp": every positive natural number has a positive natural
  power at every natural exponent. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and 0 < n is the exact SetMM
  rendering of nat.lt nat.O n. The source exponentiation satisfies
  exp n 0 = 1 and exp n (m + 1) = (exp n m) * n, so SetMM's native natural
  power n ^ m is its definitionally equivalent rendering. The declaration is
  an unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d m n $.

  logipedia-exp-lt-o-exp $a |-
    A. n e. NN0 A. m e. NN0
      ( 0 < n -> 0 < ( n ^ m ) )
  $.
$}
