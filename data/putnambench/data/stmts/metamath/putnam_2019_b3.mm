$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_b3: a Householder reflection composed with a positive-
  dimensional real orthogonal matrix has eigenvalue one when the original
  matrix does not. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN, 0 ..^ n is the canonical n-element index set. The matrix
  variables Q and P range over all real n-by-n matrices, while u ranges over
  all real n-vectors. The two quantified dot-product conditions say exactly
  that the distinct rows and columns of Q are orthogonal and that every row
  and column has norm one.

  The finite sum of the squared coordinates of u is its squared norm. The
  displayed entrywise definition of P is I - 2 u u^T. SetMM's maMul and
  maDet are real matrix multiplication and determinant. Subtracting the
  Kronecker-delta matrix is subtraction of the identity, so the conclusion
  states det(PQ - I) = 0 under the hypothesis det(Q - I) != 0.

  The zero determinant conclusion follows the published problem and the
  Lean ground truth; the opposite final inequality in the Isabelle source is
  a transcription error. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d P Q i j k n u $.

  putnambench-putnam-2019-b3 $a |- A. n e. NN
    A. Q e.
      (
        RR
        ^m
        ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
      )
      A. u e. ( RR ^m ( 0 ..^ n ) )
        A. P e.
          (
            RR
            ^m
            ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
          )
          (
            (
              (
                A. i e. ( 0 ..^ n )
                  A. j e. ( 0 ..^ n )
                    (
                      i =/= j
                      ->
                      (
                        (
                          sum_ k e. ( 0 ..^ n )
                            (
                              ( Q ` <. i , k >. )
                              x.
                              ( Q ` <. j , k >. )
                            )
                        )
                        =
                        0
                        /\
                        (
                          sum_ k e. ( 0 ..^ n )
                            (
                              ( Q ` <. k , i >. )
                              x.
                              ( Q ` <. k , j >. )
                            )
                        )
                        =
                        0
                      )
                    )
                /\
                A. i e. ( 0 ..^ n )
                  (
                    (
                      sum_ k e. ( 0 ..^ n )
                        (
                          ( Q ` <. i , k >. )
                          x.
                          ( Q ` <. i , k >. )
                        )
                    )
                    =
                    1
                    /\
                    (
                      sum_ k e. ( 0 ..^ n )
                        (
                          ( Q ` <. k , i >. )
                          x.
                          ( Q ` <. k , i >. )
                        )
                    )
                    =
                    1
                  )
              )
              /\
              (
                (
                  sum_ k e. ( 0 ..^ n )
                    (
                      ( u ` k )
                      x.
                      ( u ` k )
                    )
                )
                =
                1
                /\
                P
                =
                (
                  i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                    (
                      if ( i = j , 1 , 0 )
                      -
                      (
                        2
                        x.
                        (
                          ( u ` i )
                          x.
                          ( u ` j )
                        )
                      )
                    )
                )
              )
            )
            ->
            (
              (
                ( ( 0 ..^ n ) maDet RRfld )
                `
                (
                  i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                    (
                      ( Q ` <. i , j >. )
                      -
                      if ( i = j , 1 , 0 )
                    )
                )
              )
              =/=
              0
              ->
              (
                ( ( 0 ..^ n ) maDet RRfld )
                `
                (
                  i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                    (
                      (
                        (
                          P
                          (
                            RRfld
                            maMul
                            <.
                              ( 0 ..^ n ) ,
                              ( 0 ..^ n ) ,
                              ( 0 ..^ n )
                            >.
                          )
                          Q
                        )
                        `
                        <. i , j >.
                      )
                      -
                      if ( i = j , 1 , 0 )
                    )
                )
              )
              =
              0
            )
          )
  $.
$}
