$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_b6: reversing the product of real three-by-two and two-by-three
  matrices whose forward product has the specified entries gives nine times
  the two-by-two identity matrix. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The sets 0 ..^ 3 and 0 ..^ 2 are the index carriers for Fin 3 and Fin 2.
  Thus a, b, and p range over exactly the real 3-by-2, 2-by-3, and 3-by-3
  matrices in the sources. RRfld maMul is SetMM's rectangular matrix
  multiplication. The maps-to expression in the conclusion is the 2-by-2
  diagonal matrix with both diagonal entries equal to 9, hence exactly 9 I.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b i j p $.

  putnambench-putnam-1969-b6 $a |-
    A. a e.
      (
        RR
        ^m
        ( ( 0 ..^ 3 ) X. ( 0 ..^ 2 ) )
      )
      A. b e.
        (
          RR
          ^m
          ( ( 0 ..^ 2 ) X. ( 0 ..^ 3 ) )
        )
        A. p e.
          (
            RR
            ^m
            ( ( 0 ..^ 3 ) X. ( 0 ..^ 3 ) )
          )
          (
            (
              (
                ( 0 p 0 ) = 8
                /\
                (
                  ( 0 p 1 ) = 2
                  /\
                  (
                    ( 0 p 2 ) = ( -u 2 )
                    /\
                    (
                      ( 1 p 0 ) = 2
                      /\
                      (
                        ( 1 p 1 ) = 5
                        /\
                        (
                          ( 1 p 2 ) = 4
                          /\
                          (
                            ( 2 p 0 ) = ( -u 2 )
                            /\
                            (
                              ( 2 p 1 ) = 4
                              /\
                              ( 2 p 2 ) = 5
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
              /\
              (
                a
                (
                  RRfld
                  maMul
                  <.
                    ( 0 ..^ 3 ) ,
                    ( 0 ..^ 2 ) ,
                    ( 0 ..^ 3 )
                  >.
                )
                b
              )
              =
              p
            )
            ->
            (
              (
                b
                (
                  RRfld
                  maMul
                  <.
                    ( 0 ..^ 2 ) ,
                    ( 0 ..^ 3 ) ,
                    ( 0 ..^ 2 )
                  >.
                )
                a
              )
              =
              (
                i e. ( 0 ..^ 2 ) , j e. ( 0 ..^ 2 ) |->
                  if ( i = j , 9 , 0 )
              )
            )
          )
  $.
$}
