$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_a4: eventual strict positivity of every coefficient in the
  homogeneous support of
  (x+y)^n (x^2-(2-epsilon)xy+y^2) when 0<epsilon<1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The polynomial is homogeneous of total degree n+2. Its coefficient of
  x^i y^(n+2-i) is

    [i>=2] binomial(n,i-2)
      - (2-epsilon) [i>=1] binomial(n,i-1)
      + binomial(n,i).

  The conditionals make the first two summands zero below their natural
  exponent ranges; binomial coefficients above n are zero. The displayed
  finite quantification over 0 <= i <= n+2 is exactly the homogeneous
  support. The published problem requires these coefficients to be
  strictly positive; off-support zero coefficients are irrelevant.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d e i n N $.

  putnambench-putnam-1971-a4 $a |-
    A. e e. ( 0 (,) 1 )
      E. N e. NN0
        A. n e. NN0
          (
            N <_ n
            ->
            A. i e. ( 0 ... ( n + 2 ) )
              0 <
              (
                (
                  if (
                    2 <_ i ,
                    ( n _C ( i - 2 ) ) ,
                    0
                  )
                  -
                  (
                    ( 2 - e )
                    x.
                    if (
                      1 <_ i ,
                      ( n _C ( i - 1 ) ) ,
                      0
                    )
                  )
                )
                +
                ( n _C i )
              )
          )
  $.
$}
