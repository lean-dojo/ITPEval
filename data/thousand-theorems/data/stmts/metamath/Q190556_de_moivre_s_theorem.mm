$(
  Statement-only formalization of Thousand Theorems corpus artifact Q190556
  (thousand-theorems__metamath__Q190556), "De Moivre's theorem": for every
  natural number n and complex number z, the nth power of cos(z) + sin(z)i
  equals cos(nz) + sin(nz)i. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The included set.mm library supplies the standard complex numbers CC,
  natural numbers including zero NN0, imaginary unit _i, complex sine and
  cosine, arithmetic operations, natural powers, equality, and restricted
  universal quantifiers. In n x. z, NN0 is canonically included in CC.

  The final $a declaration is the single unproved corpus statement; there is
  no $p proof statement.
$)

thousand-theorems-q190556-de-moivre $a |- A. n e. NN0 A. z e. CC
  ( ( ( cos ` z ) + ( ( sin ` z ) x. _i ) ) ^ n ) =
    ( ( cos ` ( n x. z ) ) + ( ( sin ` ( n x. z ) ) x. _i ) ) )
$.
