$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_b6: every positive triple of natural numbers can reach a triple
  containing zero by finitely many permitted doubling-and-subtraction
  transitions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ 3 is {0,1,2}, so NN0 ^m ( 0 ..^ 3 ) is exactly the
  source type Fin 3 -> Nat. The curried source transition f(i)(j)(T) is
  represented equivalently by a total function on nested triples
  <. i , <. j , T >. >.; this is a bijective reassociation of its arguments.

  The two implications in the transition specification are the two branches
  of the source if-expression. For distinct i and j, the third index k makes
  the first branch specify all three coordinates. The existential trajectory
  is the full natural-indexed sequence used in both ground truths, and n < N is
  exactly the Fin N / {0..<N} step range. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d N S T f i j k n q $.

  putnambench-putnam-1993-b6 $a |-
    A. S e. ( NN0 ^m ( 0 ..^ 3 ) )
      A. f e.
        (
          ( NN0 ^m ( 0 ..^ 3 ) )
          ^m
          (
            ( 0 ..^ 3 )
            X.
            (
              ( 0 ..^ 3 )
              X.
              ( NN0 ^m ( 0 ..^ 3 ) )
            )
          )
        )
        (
          (
            A. i e. ( 0 ..^ 3 )
              0 < ( S ` i )
            /\
            A. i e. ( 0 ..^ 3 )
              A. j e. ( 0 ..^ 3 )
                A. k e. ( 0 ..^ 3 )
                  (
                    (
                      (
                        i =/= j
                        /\
                        i =/= k
                      )
                      /\
                      j =/= k
                    )
                    ->
                    A. T e. ( NN0 ^m ( 0 ..^ 3 ) )
                      (
                        (
                          ( T ` i ) <_ ( T ` j )
                          ->
                          (
                            (
                              (
                                (
                                  f
                                  `
                                  <. i , <. j , T >. >.
                                )
                                `
                                i
                              )
                              =
                              ( 2 x. ( T ` i ) )
                              /\
                              (
                                (
                                  f
                                  `
                                  <. i , <. j , T >. >.
                                )
                                `
                                j
                              )
                              =
                              ( ( T ` j ) - ( T ` i ) )
                            )
                            /\
                            (
                              (
                                f
                                `
                                <. i , <. j , T >. >.
                              )
                              `
                              k
                            )
                            =
                            ( T ` k )
                          )
                        )
                        /\
                        (
                          -.
                          (
                            ( T ` i )
                            <_
                            ( T ` j )
                          )
                          ->
                          (
                            f
                            `
                            <. i , <. j , T >. >.
                          )
                          =
                          T
                        )
                      )
                  )
          )
          ->
          E. q e.
            (
              ( NN0 ^m ( 0 ..^ 3 ) )
              ^m
              NN0
            )
            E. N e. NN0
              (
                ( q ` 0 ) = S
                /\
                (
                  E. i e. ( 0 ..^ 3 )
                    (
                      ( q ` N )
                      `
                      i
                    )
                    =
                    0
                  /\
                  A. n e. NN0
                    (
                      n < N
                      ->
                      E. i e. ( 0 ..^ 3 )
                        E. j e. ( 0 ..^ 3 )
                          (
                            i =/= j
                            /\
                            (
                              f
                              `
                              <. i , <. j , ( q ` n ) >. >.
                            )
                            =
                            ( q ` ( n + 1 ) )
                          )
                    )
                )
              )
        )
  $.
$}
