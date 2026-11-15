$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_b6: every integer-coefficient monic cubic has a positive
  integer input whose value is not an integer square. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  ZZ and NN are SetMM's classes of integers and positive integers. The
  square condition is stated directly in integer arithmetic. This also handles
  negative cubic values correctly: no negative integer is an integer square.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c k n $.

  putnambench-putnam-1998-b6 $a |-
    A. a e. ZZ A. b e. ZZ A. c e. ZZ
      E. n e. NN
        A. k e. ZZ
          (
            (
              ( n ^ 3 )
              +
              ( a x. ( n ^ 2 ) )
            )
            +
            (
              ( b x. n )
              +
              c
            )
          )
          =/=
          ( k x. k )
  $.
$}
