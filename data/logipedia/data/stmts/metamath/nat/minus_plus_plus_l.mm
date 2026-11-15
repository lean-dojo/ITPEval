$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_plus_plus_l (logipedia__metamath__nat.minus_plus_plus_l), catalog
  title "nat.minus_plus_plus_l": for all natural numbers x, y, and h, adding
  h to both inputs preserves their truncated natural difference. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition represents nat.plus. For natural
  numbers u and v, the term if ( v <_ u , u - v , 0 ) exactly represents
  the source total subtraction nat.minus u v: ordinary subtraction when v is
  at most u, and zero otherwise. Native equality represents logic.eq at the
  natural-number type. The three restricted universal quantifiers preserve
  the source binder order and scopes, with no assumptions. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-minus-plus-plus-l $a |-
  A. x e. NN0
    A. y e. NN0
      A. h e. NN0
        if (
          ( y + h ) <_ ( x + h ) ,
          ( ( x + h ) - ( y + h ) ) ,
          0
        )
        =
        if (
          y <_ x ,
          ( x - y ) ,
          0
        )
$.
