$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_a4: evaluation of a normalized finite sum of weighted
  binomial coefficients for every positive integer. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The summation index runs from zero through floor(n / 2), inclusively.
  Throughout this range n - 2k is nonnegative, so the displayed ordinary
  subtraction agrees with the natural subtraction in the Lean and Isabelle
  sources. The right side inlines the explicit solution from the Rocq source
  and the solution annotations in the Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k n $.

  putnambench-putnam-1974-a4 $a |- A. n e. NN
    (
      (
        1
        /
        ( 2 ^ ( n - 1 ) )
      )
      x.
      sum_ k e. ( 0 ... ( |_ ` ( n / 2 ) ) )
        (
          ( n - ( 2 x. k ) )
          x.
          ( n _C k )
        )
      =
      (
        (
          n
          /
          ( 2 ^ ( n - 1 ) )
        )
        x.
        (
          ( n - 1 )
          _C
          ( |_ ` ( n / 2 ) )
        )
      )
    )
  $.
$}
