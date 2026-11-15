$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_minus_l
  (logipedia__metamath__nat.monotonic_le_minus_l), catalog title
  "nat.monotonic_le_minus_l": for all natural numbers p, q, and n, if q is
  at most p, then subtracting n from both sides using truncated natural
  subtraction preserves that order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For natural numbers x and y, the term

    if ( y <_ x , x - y , 0 )

  exactly represents the source total subtraction nat.minus x y: ordinary
  subtraction when y is at most x, and zero otherwise. SetMM's native
  non-strict order represents nat.le. The three restricted universal
  quantifiers and implication preserve the source binder order, scopes,
  assumption, and conclusion. The final declaration is Metamath's native
  unproved $a statement encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-monotonic-le-minus-l $a |-
  A. p e. NN0
    A. q e. NN0
      A. n e. NN0
        (
          q <_ p
          ->
          if (
            n <_ q ,
            ( q - n ) ,
            0
          )
          <_
          if (
            n <_ p ,
            ( p - n ) ,
            0
          )
        )
$.
