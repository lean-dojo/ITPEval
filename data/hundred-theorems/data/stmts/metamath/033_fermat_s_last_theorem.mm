$(
  Statement-only formalization of "Fermat's Last Theorem" from Hundred
  Theorems item 033. This file contains no proof.
$)

$[ library/set.mm $]

$(
  There are no positive natural numbers a, b, and c and natural exponent n
  greater than two such that a^n + b^n = c^n. The declaration below is the
  unproved statement itself.
$)

${
  $d a b c n $.

  hundred-theorems-033-fermat-last-theorem $a |- -.
    E. n e. ( ZZ>= ` 3 )
      E. a e. NN E. b e. NN E. c e. NN
        ( ( a ^ n ) + ( b ^ n ) ) = ( c ^ n )
  $.
$}
