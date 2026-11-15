$(
  Statement-only formalization of "B&eacute;zout's Theorem" from Hundred Theorems
  item 060: every pair of integers has integer coefficients whose linear
  combination equals their greatest common divisor. This file contains no
  proof.
$)

$[ library/set.mm $]

${
  $d x y u v $.

  hundred-theorems-060-bezout $a
    |- A. x e. ZZ A. y e. ZZ
         E. u e. ZZ E. v e. ZZ
           ( x gcd y ) = ( ( x x. u ) + ( y x. v ) )
  $.
$}
