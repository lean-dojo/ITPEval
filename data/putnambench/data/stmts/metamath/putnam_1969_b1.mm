$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_b1: for every positive integer whose successor is divisible
  by 24, the sum of all its positive divisors is divisible by 24.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, so quantification over NN
  incorporates the source assumption n > 0. The class
  { d e. NN | d || n } is exactly the set of natural divisors of n; because
  n is positive, it agrees with both source divisor sets. The sum_ binder
  therefore sums every divisor once.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d d n $.

  putnambench-putnam-1969-b1 $a |-
    A. n e. NN
      (
        ; 2 4 || ( n + 1 )
        ->
        ; 2 4 || sum_ d e. { d e. NN | d || n } d
      )
  $.
$}
