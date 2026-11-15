$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_b2: evaluation of an infinite real series whose terms use a
  quotient of two finite products, under absolute-value conditions on its
  two real parameters. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P ranges over all real-valued sequences indexed by NN0. For positive j,
  0 ..^ j is the half-open natural interval from 0 through j - 1, while
  1 ... j is the inclusive interval from 1 through j. Thus the defining
  hypothesis for P is exactly

    P_j = product_(0 <= i < j) (1 - z x^i)
          / product_(1 <= i <= j) (z - x^i).

  The sum over NN is set.mm's convergent infinite real-series sum, matching
  the direct infinite sums in the Lean and Isabelle sources and equivalently
  the limit of partial sums in the Rocq source. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d P i j x z $.

  putnambench-putnam-1990-b2 $a |-
    A. x e. RR
      A. z e. RR
        A. P e. ( RR ^m NN0 )
          (
            (
              (
                ( abs ` x ) < 1
                /\
                1 < ( abs ` z )
              )
              /\
              A. j e. NN
                ( P ` j )
                =
                (
                  (
                    prod_ i e. ( 0 ..^ j )
                      ( 1 - ( z x. ( x ^ i ) ) )
                  )
                  /
                  (
                    prod_ i e. ( 1 ... j )
                      ( z - ( x ^ i ) )
                  )
                )
            )
            ->
            (
              1
              +
              sum_ j e. NN
                (
                  ( 1 + ( x ^ j ) )
                  x.
                  ( P ` j )
                )
            )
            =
            0
          )
  $.
$}
