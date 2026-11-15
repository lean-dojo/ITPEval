$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_a2: for every nonnegative integer k, the finite sum of
  2^(k-j) times the binomial coefficient (k+j choose j), from j = 0 through
  k, equals 4^k. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, 0 ... k is the inclusive
  interval from 0 through k, _C is the binomial coefficient operation, and
  sum_ is finite summation. Since every summation index j satisfies j <= k,
  the subtraction k - j is the source natural-number subtraction. The
  right-hand side inlines the solution function k |-> 4^k identified by the
  ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d j k $.

  putnambench-putnam-2020-a2 $a |-
    A. k e. NN0
      (
        (
          sum_ j e. ( 0 ... k )
            (
              ( 2 ^ ( k - j ) )
              x.
              ( ( k + j ) _C j )
            )
        )
        =
        ( 4 ^ k )
      )
  $.
$}
