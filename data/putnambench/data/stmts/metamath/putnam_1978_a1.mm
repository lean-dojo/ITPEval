$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_a1: every 20-element subset of the 34 integers
  1, 4, 7, ..., 100 contains two distinct elements whose sum is 104.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The progression is represented as the set of integers 3j + 1 with
  integer index 0 <= j <= 33. The arbitrary sets S and T, the exact
  cardinality assumption, and both internally existential witnesses are
  preserved from the source statements.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d S T j k m n $.

  putnambench-putnam-1978-a1 $a |-
    (
      (
        S = {
          k e. ZZ |
          E. j e. ( 0 ... ( ( 3 x. 9 ) + 6 ) )
            k = ( ( 3 x. j ) + 1 )
        }
        /\
        (
          T C_ S
          /\
          ( # ` T ) = ( 2 x. ( 9 + 1 ) )
        )
      )
      ->
      E. m e. T E. n e. T
        (
          m =/= n
          /\
          ( m + n ) = ( ( ( 9 + 1 ) x. ( 9 + 1 ) ) + 4 )
        )
    )
  $.
$}
