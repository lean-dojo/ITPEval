$(
  Statement-only formalization of "e is Transcendental" from Hundred
  Theorems artifact 067 (hundred-theorems__metamath__067): Euler's number,
  the exponential of one, is not algebraic. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The imported SetMM library defines _e as exp(1) and AA as the class of
  complex algebraic numbers, equivalently the roots of nonzero integer
  polynomials. Since _e is real and hence complex, the non-membership
  assertion below is exactly the transcendence statement shared by the
  sources. The final declaration is an unproved $a statement.
$)

hundred-theorems-067-e-is-transcendental $a
  |- _e e/ AA
$.
