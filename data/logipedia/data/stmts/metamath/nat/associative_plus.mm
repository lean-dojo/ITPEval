$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.associative_plus (logipedia__metamath__nat.associative_plus), catalog
  title "nat.associative_plus": natural-number addition is associative, so
  for all natural numbers x, y, and z, (x + y) + z equals x + (y + z).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native equality represent
  the source plus operation and natural-number equality. The three restricted
  universal quantifiers preserve the source binder order and scopes. The final
  declaration is Metamath's native unproved $a statement encoding.
$)

logipedia-nat-associative-plus $a |-
  A. x e. NN0
    A. y e. NN0
      A. z e. NN0
        ( ( ( x + y ) + z ) = ( x + ( y + z ) ) )
$.
