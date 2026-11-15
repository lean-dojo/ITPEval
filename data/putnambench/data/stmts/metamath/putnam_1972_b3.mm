$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_b3: group elements satisfying ABA = BA^2B, A^3 = 1, and
  an odd positive power of B equal to 1 must have B = 1. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp supplies an arbitrary group, Base ` G is its carrier,
  +g ` G is its group operation, 0g ` G is its identity, and .g ` G is
  integer group exponentiation with the exponent as the first argument.
  The witness n ranges over the positive integers NN, so 2n - 1 is precisely
  the source's positive odd exponent.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B G n $.

  putnambench-putnam-1972-b3 $a |-
    A. G A. A e. ( Base ` G ) A. B e. ( Base ` G )
      (
        (
          G e. Grp
          /\
          (
            (
              ( A ( +g ` G ) B ) ( +g ` G ) A
            )
            =
            (
              ( B ( +g ` G ) ( 2 ( .g ` G ) A ) )
              ( +g ` G )
              B
            )
            /\
            (
              ( 3 ( .g ` G ) A ) = ( 0g ` G )
              /\
              E. n e. NN
                (
                  ( ( ( 2 x. n ) - 1 ) ( .g ` G ) B )
                  =
                  ( 0g ` G )
                )
            )
          )
        )
        ->
        B = ( 0g ` G )
      )
  $.
$}
