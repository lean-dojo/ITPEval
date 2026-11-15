$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_a2: among real polynomials of degree n at least two, the
  largest possible number of negative coefficients in the square is
  2n - 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier Base ` ( Poly1 ` RRfld ) is Set.mm's ring of arbitrary
  finite-support real-coefficient univariate polynomials. P22A2NegCount maps
  such a polynomial P to the cardinality of the set of negative coefficients
  of P squared. This agrees with counting through the degree of P squared,
  since every later coefficient is zero.

  The condition that coefficient n is nonzero and every coefficient after n
  vanishes is exactly that the polynomial has degree n. The final assertion
  gives both the universal upper bound and an internally existential
  polynomial attaining 2n - 2, hence is equivalent to the claimed maximum.
  Every declaration below is an unproved $a statement encoding; this database
  contains no $p proof statement.
$)

$c P22A2NegCount $.

p22a2-neg-count-syntax $a class P22A2NegCount $.

${
  $d P i $.

  p22a2-neg-count-definition $a |- P22A2NegCount =
    (
      P e. ( Base ` ( Poly1 ` RRfld ) ) |->
        #
        `
        {
          i e. NN0 |
            (
              (
                coe1
                `
                (
                  P
                  ( .r ` ( Poly1 ` RRfld ) )
                  P
                )
              )
              `
              i
            )
            < 0
        }
    )
  $.
$}

${
  $d P j n $.

  putnambench-putnam-2022-a2 $a |- A. n e. NN0
    (
      2 <_ n
      ->
      (
        A. P e. ( Base ` ( Poly1 ` RRfld ) )
          (
            (
              ( ( coe1 ` P ) ` n ) =/= 0
              /\
              A. j e. NN0
                (
                  n < j
                  ->
                  ( ( coe1 ` P ) ` j ) = 0
                )
            )
            ->
            ( P22A2NegCount ` P ) <_ ( ( 2 x. n ) - 2 )
          )
        /\
        E. P e. ( Base ` ( Poly1 ` RRfld ) )
          (
            (
              ( ( coe1 ` P ) ` n ) =/= 0
              /\
              A. j e. NN0
                (
                  n < j
                  ->
                  ( ( coe1 ` P ) ` j ) = 0
                )
            )
            /\
            ( P22A2NegCount ` P ) = ( ( 2 x. n ) - 2 )
          )
      )
    )
  $.
$}
