$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_minus_O (logipedia__metamath__nat.eq_minus_O), catalog title
  "nat.eq_minus_O": for all natural numbers n and m, if n is at most m,
  then truncated natural subtraction n minus m equals zero. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's non-strict order represents nat.le.
  The term if ( m <_ n , n - m , 0 ) exactly represents the source total
  subtraction nat.minus n m: ordinary subtraction when m is at most n and
  zero otherwise. Native equality represents logic.eq at the natural-number
  type. The restricted universal quantifiers and implication preserve the
  source binder order, scopes, assumption, and conclusion. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-eq-minus-O $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n <_ m
        ->
        if (
          m <_ n ,
          ( n - m ) ,
          0
        )
        =
        0
      )
$.
