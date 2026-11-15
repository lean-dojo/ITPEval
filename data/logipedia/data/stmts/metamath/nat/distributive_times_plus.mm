$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.distributive_times_plus
  (logipedia__metamath__nat.distributive_times_plus), catalog title
  "nat.distributive_times_plus": left multiplication distributes over
  addition on natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total multiplication, total addition, and
  native equality represent the source times, plus, and equality operations.
  The three restricted universal quantifiers preserve the source binder order
  and scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-distributive-times-plus $a |-
  A. a e. NN0
    A. b e. NN0
      A. c e. NN0
        ( ( a x. ( b + c ) ) = ( ( a x. b ) + ( a x. c ) ) )
$.
