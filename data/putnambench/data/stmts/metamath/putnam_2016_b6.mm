$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_b6: evaluation of an alternating series whose terms contain
  reciprocal series over powers of two. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers and NN0 is the class of
  nonnegative integers. Thus the outer and inner sum_ binders preserve the
  source indices k >= 1 and n >= 0 exactly. Their nesting also preserves the
  source order: for each k, first form the reciprocal series over n, then form
  the alternating series over k.

  The right side is the published value 1, supplied explicitly by the Rocq
  source. The Rocq summand's inner denominator omits the successor on its
  zero-based outer index; the expression below follows the published problem
  and the mutually consistent Lean and Isabelle denominators instead.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k n $.

  putnambench-putnam-2016-b6 $a |-
    (
      sum_ k e. NN
        (
          (
            ( ( -u 1 ) ^ ( k - 1 ) )
            /
            k
          )
          x.
          (
            sum_ n e. NN0
              (
                1
                /
                (
                  ( k x. ( 2 ^ n ) )
                  +
                  1
                )
              )
          )
        )
    )
    =
    1
  $.
$}
