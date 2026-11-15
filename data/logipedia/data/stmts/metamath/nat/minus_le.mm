$(
  Statement-only formalization of the Logipedia corpus artifact nat.minus_le
  (logipedia__metamath__nat.minus_le), catalog title "nat.minus_le": for all
  natural numbers x and y, truncated subtraction x minus y is less than or
  equal to x. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and preserves both source
  natural-number domains. For natural numbers x and y, the term
  if ( y <_ x , x - y , 0 ) is exactly the source total subtraction
  nat.minus x y: ordinary subtraction when y is at most x, and zero otherwise.
  SetMM's native non-strict order represents nat.le. The two restricted
  universal quantifiers preserve the source binder order and scopes, with no
  assumptions. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-minus-le $a |-
  A. x e. NN0
    A. y e. NN0
      if (
        y <_ x ,
        ( x - y ) ,
        0
      )
      <_
      x
$.
