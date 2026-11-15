$(
  Statement-only formalization of the Logipedia corpus artifact nat.minus_O_n
  (logipedia__metamath__nat.minus_O_n), catalog title "nat.minus_O_n": for
  every natural number n, truncated natural subtraction of n from zero equals
  zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O. On NN0, the term
  if ( n <_ 0 , 0 - n , 0 ) exactly represents the source total subtraction
  nat.minus O n: ordinary subtraction when n is at most zero and zero
  otherwise. Native equality represents logic.eq at the natural-number type.
  The restricted universal quantifier preserves the source binder and its
  scope. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-minus-O-n $a |-
  A. n e. NN0
    (
      0
      =
      if (
        n <_ 0 ,
        ( 0 - n ) ,
        0
      )
    )
$.
