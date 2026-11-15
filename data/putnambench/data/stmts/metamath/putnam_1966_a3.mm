$(
  Statement-only formalization of PutnamBench artifact putnam_1966_a3:
  convergence to one of n times the nth term of a real sequence satisfying
  x(1) in the open unit interval and x(n+1) = x(n)(1-x(n)) for n >= 1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over every real-valued sequence indexed by the nonnegative
  integers. Quantification over NN in the recurrence is exactly
  quantification over natural indices n >= 1. The conclusion uses set.mm's
  real-sequence convergence relation for the NN0-indexed sequence
  n |-> n * A(n).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A n $.

  putnambench-putnam-1966-a3 $a |- A. A e. ( RR ^m NN0 )
    (
      (
        (
          0 < ( A ` 1 )
          /\
          ( A ` 1 ) < 1
        )
        /\
        A. n e. NN
          ( A ` ( n + 1 ) )
          =
          (
            ( A ` n )
            x.
            ( 1 - ( A ` n ) )
          )
      )
      ->
      (
        n e. NN0 |->
          ( n x. ( A ` n ) )
      )
      ~~>
      1
    )
  $.
$}
