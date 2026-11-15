$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.commutative_plus (logipedia__metamath__nat.commutative_plus), catalog
  title "nat.commutative_plus": natural-number addition is commutative, so
  for all natural numbers n and m, n + m equals m + n. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native equality represent
  the source plus operation and natural-number equality. The two restricted
  universal quantifiers preserve the source binder order and scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-commutative-plus $a |-
  A. n e. NN0
    A. m e. NN0
      ( ( n + m ) = ( m + n ) )
$.
