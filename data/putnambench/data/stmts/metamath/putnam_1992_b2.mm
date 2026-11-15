$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_b2: the coefficient of x^k in
  (1 + x + x^2 + x^3)^n equals a finite sum of products of binomial
  coefficients. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, Poly1 ` ZZring is its
  finite-support univariate polynomial ring over the integers, var1 is the
  indeterminate, and coe1 extracts the natural-indexed coefficient function.
  The source polynomial has natural coefficients; its canonical image in the
  integer polynomial ring has exactly the same nonnegative integer
  coefficients, so this coefficient representation is bidirectionally
  equivalent to the source definition of Q.

  The antecedent retains the source definition of the curried function Q for
  every n and k. The inclusive interval 0 ... k, _C, and sum_ are respectively
  the source index range, binomial coefficient, and finite sum. Set.mm's
  binomial coefficient is zero outside its standard range, while the explicit
  conditional preserves the source's truncated natural subtraction.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d Q j k n $.

  putnambench-putnam-1992-b2 $a |-
    A. Q e. ( ( NN0 ^m NN0 ) ^m NN0 )
      (
        A. n e. NN0
          A. k e. NN0
            ( ( Q ` n ) ` k )
            =
            (
              ( coe1 `
                (
                  n
                  ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                  (
                    (
                      (
                        ( 1r ` ( Poly1 ` ZZring ) )
                        ( +g ` ( Poly1 ` ZZring ) )
                        ( var1 ` ZZring )
                      )
                      ( +g ` ( Poly1 ` ZZring ) )
                      (
                        2
                        ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                        ( var1 ` ZZring )
                      )
                    )
                    ( +g ` ( Poly1 ` ZZring ) )
                    (
                      3
                      ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                      ( var1 ` ZZring )
                    )
                  )
                )
              )
              ` k
            )
        ->
        A. n e. NN0
          A. k e. NN0
            ( ( Q ` n ) ` k )
            =
            sum_ j e. ( 0 ... k )
              (
                ( n _C j )
                x.
                if
                  (
                    ( 2 x. j ) <_ k ,
                    ( n _C ( k - ( 2 x. j ) ) ) ,
                    0
                  )
              )
      )
  $.
$}
