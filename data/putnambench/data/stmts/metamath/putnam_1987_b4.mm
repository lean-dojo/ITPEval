$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_b4: convergence and values of the two real sequences defined
  by the stated coupled trigonometric recurrence. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  X and Y range over arbitrary real-valued sequences indexed by the
  nonnegative integers. The initial pair (0.8, 0.6) is written exactly as
  (4/5, 3/5), and quantification over NN imposes both recurrences at precisely
  the source indices n >= 1.

  The conclusions use set.mm's real-sequence convergence relation. Inlining
  the annotated solution (True, -1, True, 0) reduces the source result to
  convergence of X to -1 and Y to 0. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d X Y n $.

  putnambench-putnam-1987-b4 $a |-
    A. X e. ( RR ^m NN0 )
    A. Y e. ( RR ^m NN0 )
      (
        (
          (
            ( X ` 1 ) = ( 4 / 5 )
            /\
            ( Y ` 1 ) = ( 3 / 5 )
          )
          /\
          (
            A. n e. NN
              ( X ` ( n + 1 ) )
              =
              (
                (
                  ( X ` n )
                  x.
                  ( cos ` ( Y ` n ) )
                )
                -
                (
                  ( Y ` n )
                  x.
                  ( sin ` ( Y ` n ) )
                )
              )
            /\
            A. n e. NN
              ( Y ` ( n + 1 ) )
              =
              (
                (
                  ( X ` n )
                  x.
                  ( sin ` ( Y ` n ) )
                )
                +
                (
                  ( Y ` n )
                  x.
                  ( cos ` ( Y ` n ) )
                )
              )
          )
        )
        ->
        (
          X ~~> ( -u 1 )
          /\
          Y ~~> 0
        )
      )
  $.
$}
