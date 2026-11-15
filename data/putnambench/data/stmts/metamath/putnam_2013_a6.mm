$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_a6: an integer-valued kernel on the integer lattice, specified
  by a 5-by-5 table and zero outside it, has a strictly positive double sum
  over every finite nonempty lattice subset. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ X. ZZ is the set of ordered pairs of integers. The function w is total
  on this lattice, and A is total on the class of its finite subsets. The
  table hypotheses below give all 25 values in the central square, while the
  following universal hypothesis makes w zero whenever either coordinate has
  absolute value greater than two.

  The nested set.mm sums range independently over the same finite set S and
  apply w to the coordinatewise difference of each ordered pair of points.
  Thus the hypothesis defining A and the final positivity assertion preserve
  the finite-set formulation in the source. The final declaration is a single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A S a b s t w $.

  putnambench-putnam-2013-a6 $a |-
    A. w e. ( ZZ ^m ( ZZ X. ZZ ) )
      A. A e. ( ZZ ^m { S e. Fin | S C_ ( ZZ X. ZZ ) } )
        (
          (
            (
              ( w ` <. ( -u 2 ) , ( -u 2 ) >. ) = ( -u 1 )
              /\
              (
                ( w ` <. 2 , ( -u 2 ) >. ) = ( -u 1 )
                /\
                (
                  ( w ` <. ( -u 2 ) , 2 >. ) = ( -u 1 )
                  /\
                  ( w ` <. 2 , 2 >. ) = ( -u 1 )
                )
              )
            )
            /\
            (
              (
                ( w ` <. ( -u 1 ) , ( -u 2 ) >. ) = ( -u 2 )
                /\
                (
                  ( w ` <. 1 , ( -u 2 ) >. ) = ( -u 2 )
                  /\
                  (
                    ( w ` <. ( -u 2 ) , ( -u 1 ) >. ) = ( -u 2 )
                    /\
                    (
                      ( w ` <. 2 , ( -u 1 ) >. ) = ( -u 2 )
                      /\
                      (
                        ( w ` <. ( -u 2 ) , 1 >. ) = ( -u 2 )
                        /\
                        (
                          ( w ` <. 2 , 1 >. ) = ( -u 2 )
                          /\
                          (
                            ( w ` <. ( -u 1 ) , 2 >. ) = ( -u 2 )
                            /\
                            ( w ` <. 1 , 2 >. ) = ( -u 2 )
                          )
                        )
                      )
                    )
                  )
                )
              )
              /\
              (
                (
                  ( w ` <. 0 , ( -u 2 ) >. ) = 2
                  /\
                  (
                    ( w ` <. ( -u 2 ) , 0 >. ) = 2
                    /\
                    (
                      ( w ` <. 2 , 0 >. ) = 2
                      /\
                      ( w ` <. 0 , 2 >. ) = 2
                    )
                  )
                )
                /\
                (
                  (
                    ( w ` <. ( -u 1 ) , ( -u 1 ) >. ) = 4
                    /\
                    (
                      ( w ` <. 1 , ( -u 1 ) >. ) = 4
                      /\
                      (
                        ( w ` <. ( -u 1 ) , 1 >. ) = 4
                        /\
                        ( w ` <. 1 , 1 >. ) = 4
                      )
                    )
                  )
                  /\
                  (
                    (
                      ( w ` <. 0 , ( -u 1 ) >. ) = ( -u 4 )
                      /\
                      (
                        ( w ` <. ( -u 1 ) , 0 >. ) = ( -u 4 )
                        /\
                        (
                          ( w ` <. 1 , 0 >. ) = ( -u 4 )
                          /\
                          ( w ` <. 0 , 1 >. ) = ( -u 4 )
                        )
                      )
                    )
                    /\
                    (
                      ( w ` <. 0 , 0 >. ) = ; 1 2
                      /\
                      (
                        A. a e. ZZ A. b e. ZZ
                          (
                            (
                              2 < ( abs ` a )
                              \/
                              2 < ( abs ` b )
                            )
                            ->
                            ( w ` <. a , b >. ) = 0
                          )
                        /\
                        A. S e. { S e. Fin | S C_ ( ZZ X. ZZ ) }
                          ( A ` S )
                          =
                          (
                            sum_ s e. S
                              (
                                sum_ t e. S
                                  (
                                    w
                                    `
                                    <.
                                      (
                                        ( 1st ` s )
                                        -
                                        ( 1st ` t )
                                      )
                                      ,
                                      (
                                        ( 2nd ` s )
                                        -
                                        ( 2nd ` t )
                                      )
                                    >.
                                  )
                              )
                          )
                      )
                    )
                  )
                )
              )
            )
          )
          ->
          A. S e. { S e. Fin | S C_ ( ZZ X. ZZ ) }
            (
              S =/= (/)
              ->
              0 < ( A ` S )
            )
        )
  $.
$}
