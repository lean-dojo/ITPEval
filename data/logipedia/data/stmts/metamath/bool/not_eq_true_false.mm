$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.not_eq_true_false, catalog title "bool.not_eq_true_false": Boolean
  truth is not equal to Boolean falsity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source Boolean type is represented by the exact two-element carrier
  { 0 , 1 }, with true represented by 1 and false by 0. SetMM inequality is
  negated equality, so the following $a declaration directly encodes the
  source proposition and is unproved; this database contains no $p proof
  declaration.
$)

logipedia-bool-not-eq-true-false $a |- 1 =/= 0 $.
