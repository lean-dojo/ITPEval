$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_b4: nonexistence of a real 2 by 2 matrix whose matrix sine,
  defined by its usual factorial power series, has entries 1, 1996, 0, 1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( ( 0 ..^ 2 ) Mat RRfld ) is the full real 2 by 2 matrix ring.
  Its multiplicative-group exponent is ordinary matrix power, including the
  identity at exponent zero. For each pair of indices, the infinite real sum
  is the corresponding entry of

    sum_n ((-1)^n / (2n+1)!) A^(2n+1).

  The nested conditional is exactly the matrix with rows (1,1996) and (0,1).
  Thus the existential proposition is precisely the source matrix-sine
  equation, and its biconditional with F. preserves the supplied solution
  False. The final declaration is an unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d a i j n $.

  putnambench-putnam-1996-b4 $a |- (
    (
      E. a e. ( Base ` ( ( 0 ..^ 2 ) Mat RRfld ) )
        A. i e. ( 0 ..^ 2 )
          A. j e. ( 0 ..^ 2 )
            (
              sum_ n e. NN0
                (
                  (
                    ( ( -u 1 ) ^ n )
                    /
                    ( ! ` ( ( 2 x. n ) + 1 ) )
                  )
                  x.
                  (
                    (
                      (
                        ( 2 x. n ) + 1
                      )
                      (
                        .g
                        `
                        (
                          mulGrp
                          `
                          ( ( 0 ..^ 2 ) Mat RRfld )
                        )
                      )
                      a
                    )
                    ` <. i , j >.
                  )
                )
              =
              if
              (
                i = 0 ,
                if ( j = 0 , 1 , ; ; ; 1 9 9 6 ) ,
                if ( j = 0 , 0 , 1 )
              )
            )
    )
    <-> F.
  ) $.
$}
