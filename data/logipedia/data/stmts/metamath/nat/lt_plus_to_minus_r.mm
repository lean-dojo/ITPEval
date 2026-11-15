$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_plus_to_minus_r
  (logipedia__metamath__nat.lt_plus_to_minus_r), catalog title
  "nat.lt_plus_to_minus_r": for all natural numbers a, b, and c, if a + b is
  strictly less than c, then a is strictly less than the truncated natural
  difference c - b. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and strict order represent nat.plus
  and nat.lt. For natural numbers c and b, the conditional
  if ( b <_ c , c - b , 0 ) is exactly the source total subtraction
  nat.minus c b: ordinary subtraction when b is at most c, and zero otherwise.
  The three restricted universal quantifiers and implication preserve the
  source binder order, scopes, assumption, and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-lt-plus-to-minus-r $a |-
  A. a e. NN0
    A. b e. NN0
      A. c e. NN0
        (
          ( a + b ) < c
          ->
          a < if ( b <_ c , ( c - b ) , 0 )
        )
$.
