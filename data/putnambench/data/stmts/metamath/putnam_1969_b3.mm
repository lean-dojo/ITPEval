$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_b3: a real sequence whose adjacent products equal their
  positive indices and whose consecutive-term ratios converge to one
  satisfies pi times the square of its first term equals two. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  T ranges over all real-valued sequences indexed by the nonnegative
  integers. Quantification over NN imposes the adjacent-product recurrence
  exactly at every index n >= 1. The map on NN0 is the full ratio sequence,
  and set.mm's ~~> relation states its convergence to 1. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d T n $.

  putnambench-putnam-1969-b3 $a |-
    A. T e. ( RR ^m NN0 )
      (
        (
          A. n e. NN
            (
              ( ( T ` n ) x. ( T ` ( n + 1 ) ) )
              =
              n
            )
          /\
          (
            n e. NN0 |->
              ( ( T ` n ) / ( T ` ( n + 1 ) ) )
          )
          ~~>
          1
        )
        ->
        ( _pi x. ( ( T ` 1 ) ^ 2 ) ) = 2
      )
  $.
$}
