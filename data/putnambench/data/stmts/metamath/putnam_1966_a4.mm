$(
  Statement-only formalization of PutnamBench artifact putnam_1966_a4:
  the formula for the integer sequence enumerating the positive nonsquares,
  defined by stepping past each perfect square. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all integer-valued sequences indexed by the nonnegative
  integers. Quantification over NN is exactly quantification over the source
  indices n >= 1. The recurrence is expressed by its exhaustive square and
  nonsquare cases, preserving the source conditional. In the nonsquare case,
  the next-term equality is placed before the negated restricted existential
  so that the existential's scope is exactly the perfect-square test.

  For n in NN, sqrt(n) is nonnegative and cannot be a nonintegral
  half-integer. Therefore floor(sqrt(n) + 1/2) is exactly the source
  nearest-integer value round(sqrt(n)), as also made explicit in the Rocq
  source. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d A m n $.

  putnambench-putnam-1966-a4 $a |- A. A e. ( ZZ ^m NN0 )
    (
      (
        ( A ` 1 ) = 2
        /\
        A. n e. NN
          (
            (
              E. m e. ZZ
                ( m ^ 2 ) = ( ( A ` n ) + 1 )
              /\
              ( A ` ( n + 1 ) ) = ( ( A ` n ) + 2 )
            )
            \/
            (
              ( A ` ( n + 1 ) ) = ( ( A ` n ) + 1 )
              /\
              -. E. m e. ZZ
                ( m ^ 2 ) = ( ( A ` n ) + 1 )
            )
          )
      )
      ->
      A. n e. NN
        ( A ` n )
        =
        (
          n
          +
          ( |_ ` ( ( sqrt ` n ) + ( 1 / 2 ) ) )
        )
    )
  $.
$}
