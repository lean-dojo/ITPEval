$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_a6: ten bijections of the integers whose finite compositions
  reach every integer from zero have at most 512 binary-exponent compositions
  stabilizing any nonempty finite set of integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The index set 0 ... 9 represents the ten source bijections. A nonempty word
  w over these indices, together with the state sequence s, records successive
  applications beginning at zero and ending at an arbitrary integer n.
  Reversing w converts this left-to-right path convention to the source's
  right-associated composition convention, so the reachability hypothesis is
  bidirectionally equivalent to the source hypothesis.

  In the conclusion, e ranges over all functions from 0 ... 9 to { 0 , 1 }.
  Each conditional factor is f_i when e_i = 1 and the identity on ZZ when
  e_i = 0. The displayed right-associated relation composition is therefore
  exactly f_0^e_0 o ... o f_9^e_9. The restricted class counts the distinct
  resulting functions whose image of A is A. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d A e f g i j n s w $.

  putnambench-putnam-1994-a6 $a |-
    A. f e. ( ( ZZ ^m ZZ ) ^m ( 0 ... 9 ) )
      (
        (
          A. i e. ( 0 ... 9 )
            ( f ` i ) : ZZ -1-1-onto-> ZZ
          /\
          A. n e. ZZ
            E. w e. ( Word ( 0 ... 9 ) \ { (/) } )
              E. s e. ( ZZ ^m ( 0 ... ( # ` w ) ) )
                (
                  (
                    ( s ` 0 ) = 0
                    /\
                    ( s ` ( # ` w ) ) = n
                  )
                  /\
                  A. j e. ( 0 ..^ ( # ` w ) )
                    ( s ` ( j + 1 ) )
                    =
                    ( ( f ` ( w ` j ) ) ` ( s ` j ) )
                )
        )
        ->
        A. A e. ( Fin i^i ~P ZZ )
          (
            A =/= (/)
            ->
            (
              #
              `
              { g e. ( ZZ ^m ZZ ) |
                (
                  E. e e. ( { 0 , 1 } ^m ( 0 ... 9 ) )
                    g
                    =
                    (
                      if
                        (
                          ( e ` 0 ) = 1 ,
                          ( f ` 0 ) ,
                          ( _I |` ZZ )
                        )
                      o.
                      (
                        if
                          (
                            ( e ` 1 ) = 1 ,
                            ( f ` 1 ) ,
                            ( _I |` ZZ )
                          )
                        o.
                        (
                          if
                            (
                              ( e ` 2 ) = 1 ,
                              ( f ` 2 ) ,
                              ( _I |` ZZ )
                            )
                          o.
                          (
                            if
                              (
                                ( e ` 3 ) = 1 ,
                                ( f ` 3 ) ,
                                ( _I |` ZZ )
                              )
                            o.
                            (
                              if
                                (
                                  ( e ` 4 ) = 1 ,
                                  ( f ` 4 ) ,
                                  ( _I |` ZZ )
                                )
                              o.
                              (
                                if
                                  (
                                    ( e ` 5 ) = 1 ,
                                    ( f ` 5 ) ,
                                    ( _I |` ZZ )
                                  )
                                o.
                                (
                                  if
                                    (
                                      ( e ` 6 ) = 1 ,
                                      ( f ` 6 ) ,
                                      ( _I |` ZZ )
                                    )
                                  o.
                                  (
                                    if
                                      (
                                        ( e ` 7 ) = 1 ,
                                        ( f ` 7 ) ,
                                        ( _I |` ZZ )
                                      )
                                    o.
                                    (
                                      if
                                        (
                                          ( e ` 8 ) = 1 ,
                                          ( f ` 8 ) ,
                                          ( _I |` ZZ )
                                        )
                                      o.
                                      if
                                        (
                                          ( e ` 9 ) = 1 ,
                                          ( f ` 9 ) ,
                                          ( _I |` ZZ )
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
                  /\
                  ( g " A ) = A
                )
              }
            )
            <_
            ; ; 5 1 2
          )
      )
  $.
$}
