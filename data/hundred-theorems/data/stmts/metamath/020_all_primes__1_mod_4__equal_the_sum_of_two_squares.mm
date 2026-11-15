$(
  Statement-only formalization of "All Primes (1 mod 4) Equal the Sum of Two
  Squares" from Hundred Theorems item 020: every natural prime congruent to
  one modulo four is a sum of two squares of natural numbers. This file
  contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies the standard class Prime of natural
  prime numbers, the nonnegative integers NN0, natural-number remainder,
  addition, exponentiation, equality, and restricted quantifiers.

  Over the natural numbers, ( p mod 4 ) = 1 is equivalent to the existence of
  k in NN0 with p = ( 4 x. k ) + 1, so this is the modulus form of the source
  hypothesis. The declaration below is an unproved $a statement and introduces
  no $p proof.
$)

${
  $d p x y $.

  hundred-theorems-020-prime-one-mod-four-sum-two-squares $a
    |- A. p e. Prime
         (
           ( p mod 4 ) = 1
           ->
           E. x e. NN0 E. y e. NN0
             p = ( ( x ^ 2 ) + ( y ^ 2 ) )
         )
  $.
$}
