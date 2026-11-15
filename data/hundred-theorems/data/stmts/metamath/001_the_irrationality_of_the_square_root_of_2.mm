$(
  Statement-only formalization of "The Irrationality of the Square Root of 2" from Hundred
  Theorems item 001: the nonnegative real square root of two is not rational. This file
  contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library defines the standard set-theoretic real and
  rational numbers, the positive square-root function, the numeral 2, and
  non-membership.  The target proposition below is an unproved $a assertion.
$)

hundred-theorems-001-sqrt2-irrational $a
  |- ( sqrt ` 2 ) e/ QQ
$.
