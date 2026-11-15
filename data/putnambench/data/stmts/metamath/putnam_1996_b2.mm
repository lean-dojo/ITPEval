$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_b2: the odd product 1 times 3 through 2n minus 1 lies
  strictly between its two stated real-power bounds for every positive
  integer n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The inclusive product over 1 ... n of 2i - 1 is exactly the source odd
  product. For positive n, both power bases are positive, so set.mm's
  complex-power operation ^c agrees with the source real-power operation.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n $.

  putnambench-putnam-1996-b2 $a |- A. n e. NN
    (
      (
        (
          ( ( ( 2 x. n ) - 1 ) / ( exp ` 1 ) )
          ^c
          ( ( ( 2 x. n ) - 1 ) / 2 )
        )
        <
        prod_ i e. ( 1 ... n ) ( ( 2 x. i ) - 1 )
      )
      /\
      (
        prod_ i e. ( 1 ... n ) ( ( 2 x. i ) - 1 )
        <
        (
          ( ( ( 2 x. n ) + 1 ) / ( exp ` 1 ) )
          ^c
          ( ( ( 2 x. n ) + 1 ) / 2 )
        )
      )
    )
  $.
$}
