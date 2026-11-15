$(
  Statement-only formalization of the Logipedia corpus artifact nat.times_Sn_m
  (logipedia__metamath__nat.times_Sn_m), catalog title "nat.times_Sn_m": for
  all natural numbers n and m, m plus n times m equals successor n times m.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition, total multiplication, and
  native equality represent nat.plus, nat.times, and logic.eq on that domain,
  while n + 1 represents nat.S n. The restricted universal quantifiers
  preserve the source binder order and scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

logipedia-nat-times-sn-m $a |-
  A. n e. NN0
    A. m e. NN0
      ( ( m + ( n x. m ) ) = ( ( n + 1 ) x. m ) )
$.
