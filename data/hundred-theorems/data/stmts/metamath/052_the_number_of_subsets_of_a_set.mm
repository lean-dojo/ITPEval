$(
  Statement-only formalization of "The Number of Subsets of a Set" from
  Hundred Theorems item 052: the power set of every finite set has cardinality
  two raised to the cardinality of the original set. This file contains no proof.
$)

$[ library/set.mm $]

$(
  In SetMM, Fin is the class of finite sets, ~P A is the power set of A,
  # ` A is its finite cardinality, and ^ is natural-number exponentiation on
  these arguments. The following declaration is an unproved $a assertion; this
  database contains no $p proof statement.
$)

ht052-number-of-subsets $a
  |- ( A e. Fin -> ( # ` ~P A ) = ( 2 ^ ( # ` A ) ) )
$.
