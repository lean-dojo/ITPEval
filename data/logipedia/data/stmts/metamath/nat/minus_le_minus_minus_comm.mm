$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_le_minus_minus_comm
  (logipedia__metamath__nat.minus_le_minus_minus_comm), catalog title
  "nat.minus_le_minus_minus_comm": for natural numbers b, c, and a with
  c at most b, subtracting b minus c from a equals subtracting b from
  a plus c, using truncated natural subtraction. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and non-strict order represent
  nat.plus and nat.le. For natural numbers x and y, the term

    if ( y <_ x , x - y , 0 )

  exactly represents the source total subtraction nat.minus x y: ordinary
  subtraction when y is at most x, and zero otherwise. Expanding both nested
  source subtraction terms this way preserves their truncated semantics.
  Native equality represents logic.eq at the natural-number type. The three
  restricted universal quantifiers and implication preserve the source binder
  order, scopes, assumption, and conclusion. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

logipedia-nat-minus-le-minus-minus-comm $a |-
  A. b e. NN0
    A. c e. NN0
      A. a e. NN0
        (
          c <_ b
          ->
          if (
            if (
              c <_ b ,
              ( b - c ) ,
              0
            )
            <_
            a ,
            (
              a
              -
              if (
                c <_ b ,
                ( b - c ) ,
                0
              )
            ) ,
            0
          )
          =
          if (
            b <_ ( a + c ) ,
            ( ( a + c ) - b ) ,
            0
          )
        )
$.
