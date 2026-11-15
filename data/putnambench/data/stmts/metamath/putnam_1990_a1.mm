$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1990_a1: the integer sequence with initial values 2, 3, and 6 and
  the specified third-order recurrence equals n factorial plus 2 to the n
  for every nonnegative integer n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ ^m NN0 is set.mm's class of all integer-valued sequences indexed by
  the nonnegative integers. The recurrence is shifted from indices n >= 3
  to n + 3 for n in NN0, exactly as in the Lean ground truth, so no truncated
  subtraction is introduced. Set.mm's ! and ^ are factorial and natural
  exponentiation.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d T n $.

  putnambench-putnam-1990-a1 $a |- A. T e. ( ZZ ^m NN0 )
    (
      (
        (
          ( T ` 0 ) = 2
          /\
          (
            ( T ` 1 ) = 3
            /\
            ( T ` 2 ) = 6
          )
        )
        /\
        A. n e. NN0
          ( T ` ( n + 3 ) )
          =
          (
            (
              ( ( n + 7 ) x. ( T ` ( n + 2 ) ) )
              -
              ( ( 4 x. ( n + 3 ) ) x. ( T ` ( n + 1 ) ) )
            )
            +
            ( ( ( 4 x. n ) + 4 ) x. ( T ` n ) )
          )
      )
      ->
      A. n e. NN0
        ( T ` n )
        =
        (
          ( ! ` n )
          +
          ( 2 ^ n )
        )
    )
  $.
$}
