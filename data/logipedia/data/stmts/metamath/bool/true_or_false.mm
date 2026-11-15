$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.true_or_false, catalog title "bool.true_or_false": every Boolean value
  is either true or false. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source Boolean type is represented by the exact two-element carrier
  { 0 , 1 }, with true represented by 1 and false by 0. The bounded universal
  quantifier and disjunction below directly preserve the source proposition.
  The $a declaration is an unproved statement encoding; this database contains
  no $p proof declaration.
$)

logipedia-bool-true-or-false $a |-
  A. b e. { 0 , 1 } ( b = 1 \/ b = 0 )
$.
