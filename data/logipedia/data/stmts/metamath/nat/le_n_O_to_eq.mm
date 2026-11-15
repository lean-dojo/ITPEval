$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_n_O_to_eq (logipedia__metamath__nat.le_n_O_to_eq), catalog title
  "nat.le_n_O_to_eq": every natural number less than or equal to zero is
  equal to zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, its native non-strict
  order on NN0 represents nat.le, and its equality represents source
  natural-number equality. The restricted universal quantifier and implication
  preserve the source binder, assumption, conclusion, and their scopes. The
  final declaration is Metamath's native unproved $a statement encoding; this
  artifact adds no $p proof declaration.
$)

logipedia-nat-le-n-O-to-eq $a |-
  A. n e. NN0
    (
      n <_ 0
      ->
      0 = n
    )
$.
