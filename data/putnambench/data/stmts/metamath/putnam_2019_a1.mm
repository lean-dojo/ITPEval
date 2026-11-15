$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_a1: the values of A^3 + B^3 + C^3 - 3ABC for nonnegative
  integers A, B, and C are exactly the nonnegative integers whose remainder
  modulo nine is neither three nor six. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the classes of integers and nonnegative integers.
  The left side of the biconditional internally quantifies the three source
  inputs over NN0. The right side inlines the solution set identified by the
  ground-truth sources. Thus the pointwise biconditional over ZZ is
  extensionally equivalent to their equality of integer sets.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B C n $.

  putnambench-putnam-2019-a1 $a |- A. n e. ZZ
    (
      (
        E. A e. NN0 E. B e. NN0 E. C e. NN0
          n =
          (
            (
              (
                ( A ^ 3 )
                +
                ( B ^ 3 )
              )
              +
              ( C ^ 3 )
            )
            -
            (
              (
                ( 3 x. A )
                x.
                B
              )
              x.
              C
            )
          )
      )
      <->
      (
        n e. NN0
        /\
        (
          ( n mod 9 ) =/= 3
          /\
          ( n mod 9 ) =/= 6
        )
      )
    )
  $.
$}
