$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_b4 (putnambench__metamath__putnam_2025_b4): a bound relating
  the sum and number of nonzero entries of a nonnegative-integer square
  matrix with a triangular zero region and unit horizontal and vertical
  increments. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For m in NN0, the carrier 0 ..^ (m+2) is the zero-based index set
  corresponding to Fin (m+2). Thus A ranges over all natural-valued
  (m+2)-by-(m+2) matrices. The first condition is the source triangular
  zero condition. The next two conditions say that each downward or
  rightward adjacent entry equals its predecessor or exceeds it by one,
  with 0 ..^ (m+1) giving exactly the valid predecessor indices.

  S is the nested finite sum of all entries, and N is the cardinality of
  the subset of index pairs at which A is nonzero. These defining
  equalities and both natural-number binders are retained explicitly from
  the source. The conclusion is exactly 3*S <= (m+4)*N, where the source's
  matrix order is n=m+2. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d A N S i j m p $.

  putnambench-putnam-2025-b4 $a |-
    A. m e. NN0
      A. A e.
        (
          NN0
          ^m
          (
            ( 0 ..^ ( m + 2 ) )
            X.
            ( 0 ..^ ( m + 2 ) )
          )
        )
        A. S e. NN0
          A. N e. NN0
            (
              (
                A. i e. ( 0 ..^ ( m + 2 ) )
                  A. j e. ( 0 ..^ ( m + 2 ) )
                    (
                      ( i + j ) <_ m
                      ->
                      ( A ` <. i , j >. ) = 0
                    )
                /\
                (
                  A. i e. ( 0 ..^ ( m + 1 ) )
                    A. j e. ( 0 ..^ ( m + 2 ) )
                      (
                        (
                          A
                          `
                          <. ( i + 1 ) , j >.
                        )
                        =
                        ( A ` <. i , j >. )
                        \/
                        (
                          A
                          `
                          <. ( i + 1 ) , j >.
                        )
                        =
                        ( ( A ` <. i , j >. ) + 1 )
                      )
                  /\
                  (
                    A. i e. ( 0 ..^ ( m + 2 ) )
                      A. j e. ( 0 ..^ ( m + 1 ) )
                        (
                          (
                            A
                            `
                            <. i , ( j + 1 ) >.
                          )
                          =
                          ( A ` <. i , j >. )
                          \/
                          (
                            A
                            `
                            <. i , ( j + 1 ) >.
                          )
                          =
                          ( ( A ` <. i , j >. ) + 1 )
                        )
                    /\
                    (
                      S
                      =
                      (
                        sum_ i e. ( 0 ..^ ( m + 2 ) )
                          (
                            sum_ j e. ( 0 ..^ ( m + 2 ) )
                              ( A ` <. i , j >. )
                          )
                      )
                      /\
                      N
                      =
                      (
                        #
                        `
                        {
                          p e.
                            (
                              ( 0 ..^ ( m + 2 ) )
                              X.
                              ( 0 ..^ ( m + 2 ) )
                            )
                          |
                          ( A ` p ) =/= 0
                        }
                      )
                    )
                  )
                )
              )
              ->
              ( 3 x. S ) <_ ( ( m + 4 ) x. N )
            )
  $.
$}
