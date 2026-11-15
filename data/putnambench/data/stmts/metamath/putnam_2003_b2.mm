$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_b2: repeated adjacent averaging of the rational sequence
  1, 1/2, ..., 1/n yields a final value strictly less than 2/n.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, so quantifying n over NN is
  equivalent to the source's natural-number parameter together with n > 0.
  The class ( QQ ^m NN0 ) ^m NN0 contains exactly the total curried
  rational-valued functions on pairs of nonnegative integer indices used by
  the Lean and Isabelle sources. Values outside the displayed triangular
  ranges are intentionally unconstrained, as they are in those sources.

  The first conjunct is the reciprocal initialization on 1 ... n. The second
  is the adjacent-average recurrence at every stage k from 1 through n - 1
  and every valid position j from 1 through n - k. The conclusion is the
  source inequality for the sole entry at the last stage.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F j k n $.

  putnambench-putnam-2003-b2 $a |-
    A. n e. NN
      A. F e. ( ( QQ ^m NN0 ) ^m NN0 )
        (
          (
            A. j e. ( 1 ... n )
              ( ( F ` 0 ) ` j ) = ( 1 / j )
            /\
            A. k e. ( 1 ... ( n - 1 ) )
              A. j e. ( 1 ... ( n - k ) )
                ( ( F ` k ) ` j )
                =
                (
                  (
                    ( ( F ` ( k - 1 ) ) ` j )
                    +
                    ( ( F ` ( k - 1 ) ) ` ( j + 1 ) )
                  )
                  /
                  2
                )
          )
          ->
          ( ( F ` ( n - 1 ) ) ` 1 ) < ( 2 / n )
        )
  $.
$}
