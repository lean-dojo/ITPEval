$(
  Statement-only formalization of "De Moivre's Theorem" from Hundred Theorems
  item 017: for every complex number z and natural number n, the nth power of
  cos(z) + i sin(z) equals cos(nz) + i sin(nz). This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies the standard set-theoretic complex
  numbers CC, natural numbers including zero NN0, imaginary unit _i, complex
  sine and cosine, arithmetic operations, exponentiation, equality, and
  restricted universal quantifiers. The product n x. z uses the canonical
  inclusion of NN0 in CC.
$)

hundred-theorems-017-de-moivre $a |- A. z e. CC A. n e. NN0
  ( ( ( cos ` z ) + ( _i x. ( sin ` z ) ) ) ^ n ) =
    ( ( cos ` ( n x. z ) ) + ( _i x. ( sin ` ( n x. z ) ) ) ) )
$.
