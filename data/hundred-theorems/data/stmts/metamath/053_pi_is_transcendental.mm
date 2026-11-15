$(
  Statement-only formalization of "Pi is Transcendental" from Hundred
  Theorems item 053: the real number pi is not algebraic. This file contains
  no proof.
$)

$[ library/set.mm $]

$(
  The imported SetMM library defines _pi as the standard real number pi and
  AA as the class of complex algebraic numbers, equivalently the roots of
  nonzero integer polynomials. Since _pi is real and hence complex, the
  non-membership assertion below states exactly that pi is transcendental.
  The final declaration is an unproved $a statement.
$)

hundred-theorems-053-pi-is-transcendental $a
  |- _pi e/ AA
$.
