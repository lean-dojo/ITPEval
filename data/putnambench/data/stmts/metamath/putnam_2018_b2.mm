$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_b2: the polynomial n + (n-1)z + ... + z^(n-1)
  has no zero in the closed complex unit disk. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, CC is the complex plane, abs
  is complex modulus, and 0 ..^ n is the coefficient index set
  {0,...,n-1}. For each such index i, natural subtraction n-i agrees with
  ordinary integer subtraction.

  Inlining the source equation for f(n,z) as the displayed finite sum is
  definitionally equivalent to quantifying over a function constrained by
  that equation. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d i n z $.

  putnambench-putnam-2018-b2 $a |-
    A. n e. NN
      A. z e. CC
        (
          ( abs ` z ) <_ 1
          ->
          (
            sum_ i e. ( 0 ..^ n )
              (
                ( n - i )
                x.
                ( z ^ i )
              )
          )
          =/=
          0
        )
  $.
$}
