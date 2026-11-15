$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.associative_times (logipedia__metamath__nat.associative_times), catalog
  title "nat.associative_times": natural-number multiplication is associative,
  so for all natural numbers x, y, and z, (x times y) times z equals x times
  (y times z). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total multiplication and native equality
  represent the source times operation and natural-number equality. The three
  restricted universal quantifiers preserve the source binder order and
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-associative-times $a |-
  A. x e. NN0
    A. y e. NN0
      A. z e. NN0
        ( ( ( x x. y ) x. z ) = ( x x. ( y x. z ) ) )
$.
