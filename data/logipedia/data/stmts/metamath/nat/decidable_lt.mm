$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.decidable_lt (logipedia__metamath__nat.decidable_lt), catalog title
  "nat.decidable_lt": for every pair of natural numbers, their strict
  less-than proposition is decidable. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native strict order represents
  nat.lt. The disjunction of that proposition with its negation exactly
  unfolds the source definition logic.decidable P := P or not P. The two
  restricted universal quantifiers preserve the source binder order and
  scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

logipedia-nat-decidable-lt $a |-
  A. n e. NN0
    A. m e. NN0
      ( n < m \/ -. n < m )
$.
