$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_plus_m_m (logipedia__metamath__nat.minus_plus_m_m), catalog title
  "nat.minus_plus_m_m": for all natural numbers n and m, subtracting m from
  n plus m using truncated natural subtraction returns n. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition represents nat.plus. For natural
  numbers x and y, the term if ( y <_ x , x - y , 0 ) exactly represents
  the source total subtraction nat.minus x y: ordinary subtraction when y is
  at most x, and zero otherwise. Native equality represents logic.eq at the
  natural-number type. The two restricted universal quantifiers preserve the
  source binder order and scopes, with no assumptions. The final declaration
  is Metamath's native unproved $a statement encoding; this artifact adds no
  $p proof declaration.
$)

logipedia-nat-minus-plus-m-m $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n
        =
        if (
          m <_ ( n + m ) ,
          ( ( n + m ) - m ) ,
          0
        )
      )
$.
