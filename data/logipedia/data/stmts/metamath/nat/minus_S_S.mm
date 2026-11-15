$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_S_S (logipedia__metamath__nat.minus_S_S), catalog title
  "nat.minus_S_S": subtracting successors of two natural numbers equals
  subtracting the original natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the source natural-number domain, and adding one represents the
  source successor. For natural numbers u and v, the term

    if ( v <_ u , u - v , 0 )

  is exactly the source total subtraction nat.minus u v: ordinary
  subtraction when v is at most u, and zero otherwise. Native equality
  represents source natural-number equality. The two restricted universal
  quantifiers preserve the source binder order and scopes, with no
  assumptions. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-minus-S-S $a |-
  A. n e. NN0
    A. m e. NN0
      if (
        ( m + 1 ) <_ ( n + 1 ) ,
        ( ( n + 1 ) - ( m + 1 ) ) ,
        0
      )
      =
      if (
        m <_ n ,
        ( n - m ) ,
        0
      )
$.
