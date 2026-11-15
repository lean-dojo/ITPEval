$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.monotonic_pred (logipedia__metamath__nat.monotonic_pred), catalog title
  "nat.monotonic_pred": the natural-number predecessor function is monotone
  for non-strict order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Each conditional exactly represents the source total
  predecessor nat.pred: it is zero at zero and k - 1 otherwise. SetMM's native
  non-strict order represents nat.le. Expanding relations.monotonic gives the
  two restricted universal quantifiers and the implication below, preserving
  the source binder scopes, assumption, and conclusion. The final declaration
  is Metamath's native unproved $a statement encoding; this artifact adds no
  $p proof declaration.
$)

logipedia-nat-monotonic-pred $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n <_ m
        ->
        if (
          n = 0 ,
          0 ,
          ( n - 1 )
        )
        <_
        if (
          m = 0 ,
          0 ,
          ( m - 1 )
        )
      )
$.
