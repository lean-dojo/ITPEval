$(
  Statement-only formalization of the Logipedia corpus artifact nat.minus_n_O
  (logipedia__metamath__nat.minus_n_O), catalog title "nat.minus_n_O": for
  every natural number n, truncated natural subtraction of zero from n equals
  n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O. On NN0, the term
  if ( 0 <_ n , n - 0 , 0 ) exactly represents the source total subtraction
  nat.minus n O: ordinary subtraction when zero is at most n and zero
  otherwise. Native equality represents logic.eq at the natural-number type.
  The restricted universal quantifier preserves the source binder and its
  scope. The final declaration is Metamath's native unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

logipedia-nat-minus-n-O $a |-
  A. n e. NN0
    (
      n
      =
      if (
        0 <_ n ,
        ( n - 0 ) ,
        0
      )
    )
$.
