$(
  Statement-only formalization of the Logipedia corpus artifact
  primes.eq_mod_to_divides
  (logipedia__metamath__primes.eq_mod_to_divides), catalog title
  "primes.eq_mod_to_divides": equal remainders modulo a positive natural
  modulus imply that the modulus divides the truncated natural-number
  difference. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Under 0 < q, SetMM's n mod q and m mod q are exactly
  the source total natural remainders div_mod.mod n q and div_mod.mod m q.
  The conditional if ( m <_ n , ( n - m ) , 0 ) is exactly the source
  truncated subtraction nat.minus n m. For NN0 values, SetMM's q || x is
  equivalent to the source relation primes.divides q x, characterized by a
  natural multiplier k satisfying x = q x. k. The restricted universal
  quantifiers and nested implications preserve the source binder order,
  assumptions, conclusion, and scopes. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d n m q $.

  logipedia-primes-eq-mod-to-divides $a |-
    A. n e. NN0 A. m e. NN0 A. q e. NN0
      (
        0 < q
        ->
        (
          ( n mod q ) = ( m mod q )
          ->
          q || if ( m <_ n , ( n - m ) , 0 )
        )
      )
  $.
$}
