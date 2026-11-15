$(
  Statement-only formalization of "The Infinitude of Primes" from Hundred
  Theorems item 011: every natural number is bounded above by a prime number.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm
  database. NN0 is the standard class of nonnegative integers, representing
  the source natural-number domain; Prime is the formally defined class of
  natural prime numbers; and <_ is the standard arithmetic order.

  The assertion directly states the non-strict formulation used by the Lean
  and Agda sources. It is equivalent to the strict-above formulation in the
  HOL Light, Isabelle, and Rocq sources: strict implies non-strict, while
  applying the non-strict statement to n + 1 produces a prime strictly above
  n. The final declaration is an unproved $a statement.
$)

hundred-theorems-011-infinitude-of-primes $a
  |- A. n e. NN0 E. p e. Prime n <_ p
$.
