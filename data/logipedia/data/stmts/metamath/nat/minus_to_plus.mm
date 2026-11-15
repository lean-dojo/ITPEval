$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.minus_to_plus (logipedia__metamath__nat.minus_to_plus), catalog title
  "nat.minus_to_plus": for all natural numbers n, m, and p, if m is at most
  n and the truncated natural difference n minus m equals p, then n equals
  m plus p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM addition and non-strict order represent
  nat.plus and nat.le. For natural numbers n and m, the term
  if ( m <_ n , n - m , 0 ) exactly represents the source total subtraction
  nat.minus n m: ordinary subtraction when m is at most n, and zero otherwise.
  Native equality represents logic.eq at the natural-number type. The three
  restricted universal quantifiers and nested implications preserve the source
  binder order, hypothesis order, conclusion, and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-minus-to-plus $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          m <_ n
          ->
          (
            if (
              m <_ n ,
              ( n - m ) ,
              0
            )
            =
            p
            ->
            n = ( m + p )
          )
        )
$.
