$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_to_lt (logipedia__metamath__nat.not_le_to_lt), catalog title
  "nat.not_le_to_lt": for all natural numbers n and m, if n is not less than
  or equal to m, then m is strictly less than n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict and strict orders
  represent nat.le and nat.lt; the strict order is equivalent to the source
  definition nat.lt x y := nat.le (nat.S x) y. Native negation represents
  connectives.Not. The restricted universal quantifiers and implication
  preserve the source binder order, assumption, conclusion, and all scopes.
  The final declaration is Metamath's native unproved $a statement encoding;
  this database contains no $p proof declaration.
$)

logipedia-nat-not-le-to-lt $a |-
  A. n e. NN0
    A. m e. NN0
      (
        -. n <_ m
        ->
        m < n
      )
$.
