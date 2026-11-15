$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_a5: the binary digit-parity sequence has no three consecutive
  equal blocks of the same positive length. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The quantified map a has the source type NN0 -> NN0. The displayed
  recurrence forces its values to be 0 and 1 and is bidirectionally equivalent
  to the source definition by parity of the number of 1 digits in the binary
  expansion: appending a binary 0 preserves that parity, while appending a
  binary 1 reverses it; conversely, induction on the binary expansion gives
  exactly the displayed recurrence from the digit-parity definition.

  SetMM's NN is the class of positive integers, and 0 ... (m - 1) is the
  inclusive range of source indices j. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d a j k m n $.

  putnambench-putnam-1992-a5 $a |-
    A. a e. ( NN0 ^m NN0 )
      (
        (
          ( a ` 0 ) = 0
          /\
          A. n e. NN0
            (
              ( a ` ( 2 x. n ) ) = ( a ` n )
              /\
              (
                a
                `
                ( ( 2 x. n ) + 1 )
              )
              =
              ( 1 - ( a ` n ) )
            )
        )
        ->
        -.
        E. k e. NN E. m e. NN
          A. j e. ( 0 ... ( m - 1 ) )
            (
              ( a ` ( k + j ) )
              =
              ( a ` ( ( k + m ) + j ) )
              /\
              (
                a
                `
                ( ( k + m ) + j )
              )
              =
              (
                a
                `
                ( ( k + ( 2 x. m ) ) + j )
              )
            )
      )
  $.
$}
