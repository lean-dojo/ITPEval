$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_plus (logipedia__metamath__nat.minus_plus), catalog title
  "nat.minus_plus": for all natural numbers n, m, and p, subtracting m and
  then p from n equals subtracting their sum from n, using truncated natural
  subtraction. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition represents nat.plus. For natural
  numbers x and y, the term

    if ( y <_ x , x - y , 0 )

  exactly represents the source total subtraction nat.minus x y: ordinary
  subtraction when y is at most x, and zero otherwise. Expanding the two
  nested subtraction terms on the left and the subtraction term on the right
  preserves their truncated semantics. Native equality represents logic.eq
  at the natural-number type. The three restricted universal quantifiers
  preserve the source binder order and scopes, with no assumptions. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-minus-plus $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        if (
          p
          <_
          if (
            m <_ n ,
            ( n - m ) ,
            0
          ) ,
          (
            if (
              m <_ n ,
              ( n - m ) ,
              0
            )
            -
            p
          ) ,
          0
        )
        =
        if (
          ( m + p ) <_ n ,
          ( n - ( m + p ) ) ,
          0
        )
$.
