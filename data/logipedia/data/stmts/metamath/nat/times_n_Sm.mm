$(
  Statement-only formalization of the Logipedia corpus artifact nat.times_n_Sm
  (logipedia__metamath__nat.times_n_Sm), catalog title "nat.times_n_Sm": for
  all natural numbers n and m, n plus n times m equals n times the successor
  of m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition, total multiplication, and
  native equality represent nat.plus, nat.times, and logic.eq on that domain,
  while m + 1 represents nat.S m. The restricted universal quantifiers
  preserve the source binder order and scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

logipedia-nat-times-n-sm $a |-
  A. n e. NN0
    A. m e. NN0
      ( ( n + ( n x. m ) ) = ( n x. ( m + 1 ) ) )
$.
