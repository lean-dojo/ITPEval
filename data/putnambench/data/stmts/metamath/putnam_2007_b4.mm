$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_b4: the number of ordered pairs of real polynomials whose
  squares sum to X^(2n) + 1 and whose degrees are strictly decreasing is
  2^(n+1). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P07B4Poly is Set.mm's ring carrier of arbitrary finite-support
  real-coefficient univariate polynomials. Ring exponentiation and addition
  express P^2 + Q^2 = X^(2n) + 1 directly.

  The internal witness d is the exact degree of P: its coefficient at d is
  nonzero and every later coefficient vanishes. Requiring every nonzero
  coefficient of Q to have index below d is equivalent to deg P > deg Q,
  including the case Q = 0. Thus the set below is bidirectionally equivalent
  to the source set of polynomial pairs. The final $a declaration is an
  unproved statement encoding; this database contains no $p proof statement.
$)

$c P07B4Poly $.

p07b4-poly-syntax $a class P07B4Poly $.

p07b4-poly-definition $a |- P07B4Poly =
  ( Base ` ( Poly1 ` RRfld ) ) $.

${
  $d d j n t $.

  putnambench-putnam-2007-b4 $a |- A. n e. NN
    (
      #
      `
      {
        t e. ( P07B4Poly X. P07B4Poly ) |
          (
            (
              (
                2
                ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
                ( 1st ` t )
              )
              ( +g ` ( Poly1 ` RRfld ) )
              (
                2
                ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
                ( 2nd ` t )
              )
            )
            =
            (
              (
                ( 2 x. n )
                ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
                ( var1 ` RRfld )
              )
              ( +g ` ( Poly1 ` RRfld ) )
              ( 1r ` ( Poly1 ` RRfld ) )
            )
            /\
            E. d e. NN0
              (
                ( ( coe1 ` ( 1st ` t ) ) ` d ) =/= 0
                /\
                (
                  A. j e. NN0
                    (
                      d < j
                      ->
                      ( ( coe1 ` ( 1st ` t ) ) ` j ) = 0
                    )
                  /\
                  A. j e. NN0
                    (
                      ( ( coe1 ` ( 2nd ` t ) ) ` j ) =/= 0
                      ->
                      j < d
                    )
                )
              )
          )
      }
    )
    =
    ( 2 ^ ( n + 1 ) )
  $.
$}
