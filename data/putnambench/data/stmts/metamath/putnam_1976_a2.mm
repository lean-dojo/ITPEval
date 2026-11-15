$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_a2: for every positive integer n, one of the two specified
  symmetric bivariate polynomials F_n and G_n is an integer polynomial in
  P = x^2 y + x y^2 and Q = x^2 + x y + y^2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordinal 2o is the two-element variable-index set. Thus
  ( 2o mPoly ZZring ) is set.mm's ring of finite-support bivariate
  polynomials over the integers, and ( 2o eval ZZring ) evaluates such a
  polynomial at an assignment from 2o to ZZ.

  The existential witness A remains inside the quantifier over n and is
  shared by the F_n and G_n alternatives. Equality is stated at every
  integer pair x,y. Since ZZ is an infinite integral domain, equality of
  integer bivariate polynomials is equivalent to equality at all integer
  pairs, so this is the extensional form of the source polynomial identity.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A i n x y $.

  putnambench-putnam-1976-a2 $a |-
    A. n e. NN0
      (
        0 < n
        ->
        E. A e. ( Base ` ( 2o mPoly ZZring ) )
          (
            A. x e. ZZ A. y e. ZZ
              (
                (
                  (
                    ( ( x + y ) ^ n )
                    -
                    ( x ^ n )
                  )
                  -
                  ( y ^ n )
                )
                =
                (
                  ( ( 2o eval ZZring ) ` A )
                  `
                  (
                    i e. 2o |->
                      if (
                        i = (/) ,
                        (
                          ( ( x ^ 2 ) x. y )
                          +
                          ( x x. ( y ^ 2 ) )
                        ) ,
                        (
                          (
                            ( x ^ 2 )
                            +
                            ( x x. y )
                          )
                          +
                          ( y ^ 2 )
                        )
                      )
                  )
                )
              )
            \/
            A. x e. ZZ A. y e. ZZ
              (
                (
                  (
                    ( ( x + y ) ^ n )
                    +
                    ( x ^ n )
                  )
                  +
                  ( y ^ n )
                )
                =
                (
                  ( ( 2o eval ZZring ) ` A )
                  `
                  (
                    i e. 2o |->
                      if (
                        i = (/) ,
                        (
                          ( ( x ^ 2 ) x. y )
                          +
                          ( x x. ( y ^ 2 ) )
                        ) ,
                        (
                          (
                            ( x ^ 2 )
                            +
                            ( x x. y )
                          )
                          +
                          ( y ^ 2 )
                        )
                      )
                  )
                )
              )
          )
      )
  $.
$}
