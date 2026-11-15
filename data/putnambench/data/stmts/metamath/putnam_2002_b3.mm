$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_b3: for every integer n greater than one, the difference
  between 1 / exp(1) and (1 - 1 / n)^n lies strictly between
  1 / (2 n exp(1)) and 1 / (n exp(1)). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source definitions e = exp(1) and
  f(n) = 1 / e - (1 - 1 / n)^n are inlined in the assertion. This is
  definitionally equivalent to quantifying e and f with those defining
  equalities. The variable n retains the source domain ZZ, and set.mm's
  integer exponentiation is used directly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-2002-b3 $a |- A. n e. ZZ
  (
    1 < n
    ->
    (
      (
        1
        /
        (
          ( 2 x. n )
          x.
          ( exp ` 1 )
        )
      )
      <
      (
        ( 1 / ( exp ` 1 ) )
        -
        ( ( 1 - ( 1 / n ) ) ^ n )
      )
      /\
      (
        (
          ( 1 / ( exp ` 1 ) )
          -
          ( ( 1 - ( 1 / n ) ) ^ n )
        )
        <
        (
          1
          /
          (
            n
            x.
            ( exp ` 1 )
          )
        )
      )
    )
  ) $.
