$(
  Statement-only formalization of Thousand Theorems corpus artifact Q193910
  (thousand-theorems__metamath__Q193910), "Euler's theorem": for all natural
  numbers x and n, if x and n are coprime, then x raised to Euler's totient of
  n is congruent to one modulo n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of natural numbers. SetMM's native Euler phi function
  is defined on positive integers, while Mathlib's Nat.totient is total and
  has value zero at zero. Q193910Phi is the corresponding totalization on
  NN0. Q193910ModEq is Mathlib's total Nat.ModEq: at modulus zero it compares
  the original naturals, and at a positive modulus it compares SetMM
  remainders. For natural numbers, gcd equal to one is Nat.Coprime.

  The auxiliary $a assertions are faithful definitions, and the final $a is
  the unproved corpus statement. This root file contains no $p proof
  declaration.
$)

$c Q193910Phi Q193910ModEq $.

q193910-phi-syntax $a class Q193910Phi $.
q193910-mod-eq-syntax $a wff ( Q193910ModEq A B M ) $.

${
  q193910-phi-definition $a |-
    Q193910Phi =
      ( n e. NN0 |-> if ( n = 0 , 0 , ( phi ` n ) ) )
  $.
$}

q193910-mod-eq-definition $a |- (
  ( Q193910ModEq A B M )
  <->
  if (
    M = 0 ,
    A ,
    ( A mod M )
  )
  =
  if (
    M = 0 ,
    B ,
    ( B mod M )
  )
) $.

${
  $d n x $.
  thousand-theorems-q193910-euler-s-theorem $a |-
    A. x e. NN0
      A. n e. NN0
        (
          ( x gcd n ) = 1
          ->
          ( Q193910ModEq ( x ^ ( Q193910Phi ` n ) ) 1 n )
        )
  $.
$}
