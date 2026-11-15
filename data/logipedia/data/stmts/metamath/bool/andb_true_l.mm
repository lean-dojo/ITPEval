$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.andb_true_l, catalog title "bool.andb_true_l": Boolean conjunction
  being true implies that its left input is true. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source Boolean type is represented by the exact two-element carrier
  { 0 , 1 }, with true represented by 1 and false by 0. On this carrier,
  multiplication is exactly the source andb operation defined by Boolean
  elimination. The following $a declaration is an unproved statement encoding.
$)

logipedia-bool-andb-true-l $a |-
  A. b e. { 0 , 1 } A. c e. { 0 , 1 }
    ( ( b x. c ) = 1 -> b = 1 )
$.
