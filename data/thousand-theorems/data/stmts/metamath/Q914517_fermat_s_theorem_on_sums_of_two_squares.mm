$(
  Statement-only formalization of Thousand Theorems corpus artifact Q914517
  (thousand-theorems__metamath__Q914517), "Fermat's theorem on sums of two
  squares": every natural prime whose remainder modulo four is not three is
  a sum of two squares of natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is SetMM's class of natural primes, so restricting p to Prime exactly
  represents the source Fact p.Prime assumption. NN0 is the standard class of
  nonnegative integers and therefore represents each source natural-number
  witness. The remainder inequality and the internally quantified witnesses
  preserve the hypothesis and conclusion of Nat.Prime.sq_add_sq, including
  the prime p = 2. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d a b p $.

  thousand-theorems-q914517-fermat-sum-two-squares $a |-
    A. p e. Prime
      (
        ( p mod 4 ) =/= 3
        ->
        E. a e. NN0
          E. b e. NN0
            ( ( a ^ 2 ) + ( b ^ 2 ) ) = p
      )
  $.
$}
