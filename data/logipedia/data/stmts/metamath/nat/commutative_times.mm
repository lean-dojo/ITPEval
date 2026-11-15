$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.commutative_times (logipedia__metamath__nat.commutative_times), catalog
  title "nat.commutative_times": natural-number multiplication is commutative,
  so for all natural numbers x and y, x times y equals y times x. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total multiplication and native equality
  represent the source times operation and natural-number equality. The two
  restricted universal quantifiers preserve the source binder order and
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-commutative-times $a |-
  A. x e. NN0
    A. y e. NN0
      ( ( x x. y ) = ( y x. x ) )
$.
