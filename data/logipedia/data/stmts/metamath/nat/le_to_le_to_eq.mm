$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_le_to_eq (logipedia__metamath__nat.le_to_le_to_eq), catalog title
  "nat.le_to_le_to_eq": two natural numbers are equal if each is less than or
  equal to the other. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native non-strict order on NN0 represents
  nat.le, and its equality represents source natural-number equality. The two
  restricted universal quantifiers and nested implications preserve the
  source binder order, hypothesis order, conclusion, and all scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-le-to-le-to-eq $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n <_ m
        ->
        (
          m <_ n
          ->
          n = m
        )
      )
$.
