$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_b3: the infinite real series formed from powers of two
  indexed by the nearest integer to each positive integer's square root
  evaluates to 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers. For n in NN, sqrt(n) cannot
  be a nonintegral half-integer, so floor(sqrt(n) + 1/2) is exactly the
  closest integer to sqrt(n). The unbounded sum_ over NN is set.mm's
  convergent infinite real-series sum. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

putnambench-putnam-2001-b3 $a |-
  (
    sum_ n e. NN
      (
        (
          ( 2 ^ ( |_ ` ( ( sqrt ` n ) + ( 1 / 2 ) ) ) )
          +
          (
            2
            ^
            ( -u ( |_ ` ( ( sqrt ` n ) + ( 1 / 2 ) ) ) )
          )
        )
        /
        ( 2 ^ n )
      )
  )
  =
  3
$.
