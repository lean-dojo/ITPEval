$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_a6: the determinant of the Hankel matrix formed from the
  coefficients of the specified algebraic real power series is
  10 raised to n(n-1)/2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is SetMM's class of real sequences indexed by the nonnegative
  integers. The internal positive radius and the convergence of the
  inclusive partial-sum sequence encode the source assertion that, for all
  sufficiently small real x, the coefficient series HasSum to the displayed
  algebraic function.

  For positive n, 0 ..^ n is the canonical zero-based n-element carrier.
  The matrix entry c(i+j+1) is therefore exactly c_(r+s-1) for the source's
  one-based row and column indices r and s. SetMM's maDet over RRfld is the
  real determinant. The floor in the exponent represents the source natural
  division by two; on positive integral n it equals n(n-1)/2.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d c d i j k m n x $.

  putnambench-putnam-2024-a6 $a |-
    A. c e. ( RR ^m NN0 )
      A. n e. NN
        (
          E. d e. RR
            (
              0 < d
              /\
              A. x e. RR
                (
                  ( abs ` x ) < d
                  ->
                  (
                    m e. NN0 |->
                      sum_ k e. ( 0 ... m )
                        (
                          ( c ` k )
                          x.
                          ( x ^ k )
                        )
                  )
                  ~~>
                  (
                    (
                      (
                        1
                        -
                        ( 3 x. x )
                      )
                      -
                      (
                        sqrt
                        `
                        (
                          (
                            1
                            -
                            ( ( ; 1 4 ) x. x )
                          )
                          +
                          (
                            9
                            x.
                            ( x ^ 2 )
                          )
                        )
                      )
                    )
                    /
                    4
                  )
                )
            )
          ->
          (
            (
              ( ( 0 ..^ n ) maDet RRfld )
              `
              (
                i e. ( 0 ..^ n ) ,
                j e. ( 0 ..^ n ) |->
                  (
                    c
                    `
                    (
                      ( i + j )
                      +
                      1
                    )
                  )
              )
            )
            =
            (
              ( ; 1 0 )
              ^
              (
                |_
                `
                (
                  (
                    n
                    x.
                    ( n - 1 )
                  )
                  /
                  2
                )
              )
            )
          )
        )
  $.
$}
