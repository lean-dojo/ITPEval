$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.decidable_le (logipedia__metamath__nat.decidable_le), catalog title
  "nat.decidable_le": for every pair of natural numbers, their less-than-or-
  equal proposition is decidable. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict order represents
  nat.le. The disjunction of that proposition with its negation exactly
  unfolds the source definition logic.decidable P := P or not P. The two
  restricted universal quantifiers preserve the source binder order and
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

logipedia-nat-decidable-le $a |-
  A. n e. NN0
    A. m e. NN0
      ( n <_ m \/ -. n <_ m )
$.
