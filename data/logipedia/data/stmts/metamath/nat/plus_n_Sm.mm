$(
  Statement-only formalization of the Logipedia corpus artifact nat.plus_n_Sm
  (logipedia__metamath__nat.plus_n_Sm), catalog title "nat.plus_n_Sm":
  successor commutes with adding a natural number on the left,
  S (n + m) = n + S m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native equality represent
  nat.plus and logic.eq on that domain, while adding 1 represents nat.S.
  The restricted universal quantifiers preserve the source binder order and
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-plus-n-sm $a |-
  A. n e. NN0
    A. m e. NN0
      ( ( ( n + m ) + 1 ) = ( n + ( m + 1 ) ) )
$.
