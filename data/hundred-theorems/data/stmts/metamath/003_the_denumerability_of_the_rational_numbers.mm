$(
  Statement-only formalization of "The Denumerability of the Rational Numbers" from Hundred
  Theorems item 003: there exists a bijection from the standard natural numbers onto the
  standard rational numbers. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library defines the natural numbers including zero as
  NN0, the rational numbers as QQ, existential quantification, and the
  one-to-one onto function predicate. The proposition below is an unproved $a
  assertion that a bijection from NN0 onto QQ exists.
$)

hundred-theorems-003-rationals-denumerable $a
  |- E. f f : NN0 -1-1-onto-> QQ
$.
