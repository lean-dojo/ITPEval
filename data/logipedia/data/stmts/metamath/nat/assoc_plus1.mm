$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.assoc_plus1 (logipedia__metamath__nat.assoc_plus1), catalog title
  "nat.assoc_plus1": for all natural numbers a, b, and c, adding c to b
  plus a equals adding a to b plus c. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native equality represent
  the source plus operation and natural-number equality. The three restricted
  universal quantifiers preserve the source binder order and scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-assoc-plus1 $a |-
  A. a e. NN0
    A. b e. NN0
      A. c e. NN0
        ( ( c + ( b + a ) ) = ( ( b + c ) + a ) )
$.
