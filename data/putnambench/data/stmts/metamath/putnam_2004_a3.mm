$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_a3: every term of the real sequence beginning with three ones
  whose consecutive two-by-two determinants equal n factorial is an integer.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is set.mm's class of all real-valued sequences indexed by the
  nonnegative integers. The determinant condition is expanded as
  u_n u_(n+3) - u_(n+1) u_(n+2) = n!, exactly matching the two-by-two matrix
  determinant in the source. Membership of each term in ZZ is equivalent to
  the source conclusion that it equals an embedded integer.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d n u $.

  putnambench-putnam-2004-a3 $a |- A. u e. ( RR ^m NN0 )
    (
      (
        (
          (
            ( u ` 0 ) = 1
            /\
            (
              ( u ` 1 ) = 1
              /\
              ( u ` 2 ) = 1
            )
          )
          /\
          A. n e. NN0
            (
              (
                ( u ` n )
                x.
                ( u ` ( n + 3 ) )
              )
              -
              (
                ( u ` ( n + 1 ) )
                x.
                ( u ` ( n + 2 ) )
              )
            )
            =
            ( ! ` n )
        )
        ->
        A. n e. NN0 ( u ` n ) e. ZZ
      )
    )
  $.
$}
