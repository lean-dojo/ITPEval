$(
  Statement-only formalization of the Logipedia corpus artifact nat.minus_n_n
  (logipedia__metamath__nat.minus_n_n), catalog title "nat.minus_n_n": for
  every natural number n, truncated natural subtraction of n from itself
  equals zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O. For a natural number n,
  the term if ( n <_ n , n - n , 0 ) exactly represents the source total
  subtraction nat.minus n n: ordinary subtraction when the second argument
  is at most the first, and zero otherwise. Native equality represents
  logic.eq at the natural-number type. The restricted universal quantifier
  preserves the source binder and its scope. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

logipedia-nat-minus-n-n $a |-
  A. n e. NN0
    (
      0
      =
      if (
        n <_ n ,
        ( n - n ) ,
        0
      )
    )
$.
