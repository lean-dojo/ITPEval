$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_a4: an all-ones rectangular submatrix of a square real
  plus-or-minus-one matrix with mutually orthogonal rows has area at most
  the order of the square matrix. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For each positive integer n, the carrier 0 ..^ n is the n-element set
  corresponding to Fin n. The matrices H and S are total real-valued
  functions on the Cartesian squares/rectangles of their index carriers;
  this is the uncurried form of the source matrices.

  Row orthogonality is expanded as the finite real sum of coordinate
  products. The internally existential maps R and C are injections selecting
  the rows and columns, and the displayed function equality says exactly
  that S is the corresponding submatrix of H. The remaining conjunct says
  every entry of S is one.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof declaration.
$)

${
  $d C H R S a b i j k n $.

  putnambench-putnam-2005-a4 $a |-
    A. n e. NN
      A. H e.
        (
          RR
          ^m
          ( ( 0 ..^ n ) X. ( 0 ..^ n ) )
        )
        A. a e. NN
          A. b e. NN
            A. S e.
              (
                RR
                ^m
                ( ( 0 ..^ a ) X. ( 0 ..^ b ) )
              )
              (
                (
                  A. i e. ( 0 ..^ n )
                    A. j e. ( 0 ..^ n )
                      (
                        ( H ` <. i , j >. ) = 1
                        \/
                        ( H ` <. i , j >. ) = ( -u 1 )
                      )
                  /\
                  (
                    A. i e. ( 0 ..^ n )
                      A. j e. ( 0 ..^ n )
                        (
                          i =/= j
                          ->
                          (
                            sum_ k e. ( 0 ..^ n )
                              (
                                ( H ` <. i , k >. )
                                x.
                                ( H ` <. j , k >. )
                              )
                          )
                          =
                          0
                        )
                    /\
                    (
                      ( a <_ n /\ b <_ n )
                      /\
                      (
                        E. R E. C
                          (
                            (
                              R : ( 0 ..^ a ) -1-1-> ( 0 ..^ n )
                              /\
                              C : ( 0 ..^ b ) -1-1-> ( 0 ..^ n )
                            )
                            /\
                            S
                            =
                            (
                              i e. ( 0 ..^ a ) ,
                              j e. ( 0 ..^ b ) |->
                                (
                                  H
                                  `
                                  <. ( R ` i ) , ( C ` j ) >.
                                )
                            )
                          )
                        /\
                        A. i e. ( 0 ..^ a )
                          A. j e. ( 0 ..^ b )
                            ( S ` <. i , j >. ) = 1
                      )
                    )
                  )
                )
                ->
                ( a x. b ) <_ n
              )
  $.
$}
