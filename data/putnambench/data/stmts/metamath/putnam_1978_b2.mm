$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_b2: evaluation of a nested positive reciprocal series over
  pairs of positive integers as 7 / 4. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. The two sum_ binders are
  unbounded series sums, so the displayed expression is the iterated sum in
  the Lean and Isabelle sources, with exactly the same denominator.

  Every summand is nonnegative. Consequently, the iterated sum is equivalent
  to the limit of the increasing square partial sums used by the Rocq source,
  since those finite squares exhaust NN X. NN. The right side is the explicit
  Rocq solution and the solution value annotated in the other sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i j $.

  putnambench-putnam-1978-b2 $a |-
    (
      sum_ i e. NN
        (
          sum_ j e. NN
            (
              1
              /
              (
                ( ( i ^ 2 ) x. j )
                +
                (
                  ( 2 x. i )
                  x.
                  j
                )
                +
                ( i x. ( j ^ 2 ) )
              )
            )
        )
    )
    =
    ( 7 / 4 )
  $.
$}
