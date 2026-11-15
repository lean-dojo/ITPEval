$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_a1: the greatest value of x^3 - 3x over the real numbers
  satisfying x^4 + 36 <= 13x^2 is 18. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function and its admissible set are inlined from their source
  definitions. The first conjunct says that every admissible real input has
  polynomial value at most 18, and the second says that an admissible real
  input attains 18. Together these are exactly the source IsGreatest
  assertion. The declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  putnambench-putnam-1986-a1 $a |-
    (
      A. x e. RR
        (
          (
            (
              ( x ^ 4 )
              +
              ( 6 x. 6 )
            )
            <_
            (
              ( ( 3 x. 4 ) + 1 )
              x.
              ( x ^ 2 )
            )
          )
          ->
          (
            (
              ( x ^ 3 )
              -
              ( 3 x. x )
            )
            <_
            ( 9 + 9 )
          )
        )
      /\
      E. x e. RR
        (
          (
            (
              ( x ^ 4 )
              +
              ( 6 x. 6 )
            )
            <_
            (
              ( ( 3 x. 4 ) + 1 )
              x.
              ( x ^ 2 )
            )
          )
          /\
          (
            (
              ( x ^ 3 )
              -
              ( 3 x. x )
            )
            =
            ( 9 + 9 )
          )
        )
    )
  $.
$}
