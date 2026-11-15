$(
  Statement-only formalization of Thousand Theorems corpus artifact Q276082
  (thousand-theorems__metamath__Q276082), "Wilson's theorem": for every prime
  natural number p, the factorial of p - 1 is equal to -1 modulo p. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is SetMM's class of natural primes. Since every prime is positive,
  SetMM subtraction and factorial in the displayed expression agree with the
  source natural-number operations. Equality of the two remainders modulo p
  is exactly equality in ZMod p after casting the factorial.

  The final declaration is the single unproved $a corpus statement. This root
  file introduces no $p proof statement.
$)

thousand-theorems-q276082-wilsons-lemma $a |-
  A. p e. Prime
    (
      ( ( ! ` ( p - 1 ) ) mod p )
      =
      ( -u 1 mod p )
    )
$.
