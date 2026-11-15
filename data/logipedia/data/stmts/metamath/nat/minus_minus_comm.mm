$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_minus_comm (logipedia__metamath__nat.minus_minus_comm), catalog
  title "nat.minus_minus_comm": for all natural numbers a, b, and c,
  subtracting b and then c from a equals subtracting c and then b, using
  truncated natural subtraction. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For natural numbers x and y, the term

    if ( y <_ x , x - y , 0 )

  exactly represents the source total subtraction nat.minus x y: ordinary
  subtraction when y is at most x, and zero otherwise. Expanding both inner
  and both outer source subtraction terms this way preserves the two nested
  truncated-subtraction expressions. SetMM's native equality represents
  logic.eq at the natural-number type. The three restricted universal
  quantifiers preserve the source binder order and scopes, with no
  assumptions. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-minus-minus-comm $a |-
  A. a e. NN0
    A. b e. NN0
      A. c e. NN0
        if (
          c
          <_
          if (
            b <_ a ,
            ( a - b ) ,
            0
          ) ,
          (
            if (
              b <_ a ,
              ( a - b ) ,
              0
            )
            -
            c
          ) ,
          0
        )
        =
        if (
          b
          <_
          if (
            c <_ a ,
            ( a - c ) ,
            0
          ) ,
          (
            if (
              c <_ a ,
              ( a - c ) ,
              0
            )
            -
            b
          ) ,
          0
        )
$.
