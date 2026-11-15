$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_plus_to_le_r (logipedia__metamath__nat.le_plus_to_le_r), catalog
  title "nat.le_plus_to_le_r": for all natural numbers a, n, and m, if
  n + a is less than or equal to m + a, then n is less than or equal to m.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native non-strict order
  represent nat.plus and nat.le. The three restricted universal quantifiers
  and implication preserve the source binder order, scopes, assumption, and
  conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

logipedia-nat-le-plus-to-le-r $a |-
  A. a e. NN0
    A. n e. NN0
      A. m e. NN0
        (
          ( n + a ) <_ ( m + a )
          ->
          n <_ m
        )
$.
