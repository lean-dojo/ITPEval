$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_le_minus_r
  (logipedia__metamath__nat.monotonic_le_minus_r), catalog title
  "nat.monotonic_le_minus_r": for all natural numbers p, q, and n, if q is
  at most p, then n minus p is at most n minus q under truncated natural
  subtraction. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. For natural numbers n and x, the term
  if ( x <_ n , n - x , 0 ) exactly represents the source total subtraction
  nat.minus n x: ordinary subtraction when x is at most n, and zero otherwise.
  SetMM's native non-strict order represents nat.le. The three restricted
  universal quantifiers preserve the source binder order p, q, n and their
  scopes; the implication preserves the sole assumption and conclusion. The
  final declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-monotonic-le-minus-r $a |-
  A. p e. NN0
    A. q e. NN0
      A. n e. NN0
        (
          q <_ p
          ->
          if (
            p <_ n ,
            ( n - p ) ,
            0
          )
          <_
          if (
            q <_ n ,
            ( n - q ) ,
            0
          )
        )
$.
