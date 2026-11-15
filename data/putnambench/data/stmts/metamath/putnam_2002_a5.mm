$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_a5: every positive rational occurs as the ratio of consecutive
  terms of the specified recursively defined rational sequence. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The class QQ ^m NN0 is the class of rational-valued sequences indexed by
  the nonnegative integers. The antecedent states the initial value and both
  recursion rules for every nonnegative integer n.

  Set.mm's NN is the class of positive integers. Thus the internally
  quantified m in the conclusion ranges over exactly the source indices
  m >= 1, and m - 1 remains a nonnegative sequence index.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a m n q $.

  putnambench-putnam-2002-a5 $a |- A. a e. ( QQ ^m NN0 )
    (
      (
        ( a ` 0 ) = 1
        /\
        A. n e. NN0
          (
            ( a ` ( ( 2 x. n ) + 1 ) ) = ( a ` n )
            /\
            ( a ` ( ( 2 x. n ) + 2 ) )
            =
            ( ( a ` n ) + ( a ` ( n + 1 ) ) )
          )
      )
      ->
      A. q e. QQ
        (
          0 < q
          ->
          E. m e. NN
            q
            =
            (
              ( a ` ( m - 1 ) )
              /
              ( a ` m )
            )
        )
    )
  $.
$}
