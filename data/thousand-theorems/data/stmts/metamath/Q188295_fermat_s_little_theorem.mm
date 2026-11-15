$(
  Statement-only formalization of Thousand Theorems corpus artifact Q188295
  (thousand-theorems__metamath__Q188295), "Fermat's little theorem": for a
  prime p, every nonzero residue class modulo p raised to the power p - 1 is
  equal to one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is SetMM's class of natural primes, and ( 0 ..^ p ) is the canonical
  set of representatives for ZMod p. For such a representative a, equality
  in ZMod p is equality of remainders modulo p. Since a and 0 are canonical
  representatives, a =/= 0 is exactly the source nonzero hypothesis.
  Therefore the assertion is a bijective representative encoding of
  ZMod.pow_card_sub_one_eq_one. The final declaration is the single unproved
  $a corpus statement; this root file contains no $p proof declaration.
$)

${
  $d a p $.

  thousand-theorems-q188295-fermat-little-theorem $a |-
    A. p e. Prime
      A. a e. ( 0 ..^ p )
        (
          a =/= 0
          ->
          ( ( a ^ ( p - 1 ) ) mod p ) = 1
        )
  $.
$}
