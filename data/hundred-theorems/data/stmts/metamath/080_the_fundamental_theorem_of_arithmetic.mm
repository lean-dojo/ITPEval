$(
  Statement-only formalization of Hundred Theorems corpus artifact 080,
  "The Fundamental Theorem of Arithmetic": positive integers correspond
  bijectively to finitely supported functions assigning nonnegative exponents
  to prime numbers. This file contains no proof.
$)

$[ library/set.mm $]

$(
  For a positive integer n and prime p, ( p pCnt n ) is the exponent of p in
  n. Thus the inner mapping is the prime-exponent function of n. The target
  class consists of functions from Prime to NN0 whose inverse image of NN is
  finite, equivalently functions with only finitely many nonzero exponents.
  The bijection states both existence and uniqueness of prime factorization.
  The final declaration is an unproved $a statement.
$)

${
  $d e n p $.

  hundred-theorems-080-fundamental-theorem-of-arithmetic $a
    |- ( n e. NN |-> ( p e. Prime |-> ( p pCnt n ) ) )
         : NN -1-1-onto->
           { e e. ( NN0 ^m Prime ) | ( `' e " NN ) e. Fin }
  $.
$}
