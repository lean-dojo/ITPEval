$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_a6: a real number whose power of every positive integer
  base is an integer is itself a nonnegative integer. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. For a positive base n,
  the complex-power operation n ^c c agrees with the source real power
  exp(c log n). Integer-valuedness and the nonnegative-integer conclusion
  are both represented with their integer witnesses internally quantified.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d c m n $.

  putnambench-putnam-1971-a6 $a |- A. c e. RR
    (
      (
        A. n e. NN E. m e. ZZ
          ( n ^c c ) = m
      )
      ->
      E. m e. ZZ
        (
          0 <_ m
          /\
          c = m
        )
    )
  $.
$}
