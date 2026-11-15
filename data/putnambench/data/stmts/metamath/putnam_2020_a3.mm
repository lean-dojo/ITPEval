$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_a3: divergence of the sum of squares of the real sequence
  beginning at pi/2 and defined by repeated application of sine. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is set.mm's class of all real-valued sequences indexed by the
  nonnegative integers. The antecedent preserves the initial value and the
  recurrence at every nonnegative index.

  For m in NN0, the mapped value is the finite sum from 1 through m of the
  squared sequence entries. The negated existential keeps the possible real
  limit internal and states that this partial-sum sequence has no finite real
  limit, which is exactly the source biconditional between convergence and
  False. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d L a m n $.

  putnambench-putnam-2020-a3 $a |- A. a e. ( RR ^m NN0 )
    (
      (
        ( a ` 0 ) = ( _pi / 2 )
        /\
        A. n e. NN0
          ( a ` ( n + 1 ) ) = ( sin ` ( a ` n ) )
      )
      ->
      -.
      E. L e. RR
        (
          m e. NN0 |->
            sum_ n e. ( 1 ... m )
              ( ( a ` n ) ^ 2 )
        )
        ~~>
        L
    )
  $.
$}
