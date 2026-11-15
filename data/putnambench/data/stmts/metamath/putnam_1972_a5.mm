$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_a5: no natural number greater than one divides one less
  than its corresponding power of two. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, and || is integer
  divisibility. For n greater than one, 2 ^ n - 1 is nonnegative, so this
  formulation agrees with Isabelle's natural subtraction and with the
  integer coercions used by the Lean and Rocq sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  putnambench-putnam-1972-a5 $a |- A. n e. NN0
    (
      1 < n
      ->
      -. n || ( ( 2 ^ n ) - 1 )
    )
  $.
$}
