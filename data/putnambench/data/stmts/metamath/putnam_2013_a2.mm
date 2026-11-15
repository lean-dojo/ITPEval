$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_a2: injectivity of the least possible final entry of a strictly
  increasing integer sequence whose product with a positive nonsquare integer
  is a perfect square. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variables n, x, and y range over all integers. The repeated conditions
  0 < n and nonexistence of an integer square root define exactly the source
  set S of positive nonsquares.

  For r in NN, a in ( ZZ ^m ( 1 ... r ) ) is a nonempty finite integer
  sequence. The first-entry bound, strict inequalities on 1 ..^ r, and the
  internally existential square witness are exactly the source predicate P.
  The first minimum clause says that f(n) is attained as a(r); the second says
  it is no larger than the final entry of every admissible sequence. Together
  they expand membership in T(n) and the source least-element condition
  without externalizing a sequence or square witness.

  The conclusion is the pointwise expansion of injectivity of f on S. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d a f i m n r x y $.

  putnambench-putnam-2013-a2 $a |-
    A. f e. ( ZZ ^m ZZ )
      (
        A. n e. ZZ
          (
            (
              0 < n
              /\
              -. E. m e. ZZ ( m ^ 2 ) = n
            )
            ->
            (
              E. r e. NN
                E. a e. ( ZZ ^m ( 1 ... r ) )
                  (
                    (
                      (
                        n < ( a ` 1 )
                        /\
                        A. i e. ( 1 ..^ r )
                          ( a ` i ) < ( a ` ( i + 1 ) )
                      )
                      /\
                      E. m e. ZZ
                        ( m ^ 2 )
                        =
                        (
                          n
                          x.
                          prod_ i e. ( 1 ... r ) ( a ` i )
                        )
                    )
                    /\
                    ( f ` n ) = ( a ` r )
                  )
              /\
              A. r e. NN
                A. a e. ( ZZ ^m ( 1 ... r ) )
                  (
                    (
                      (
                        n < ( a ` 1 )
                        /\
                        A. i e. ( 1 ..^ r )
                          ( a ` i ) < ( a ` ( i + 1 ) )
                      )
                      /\
                      E. m e. ZZ
                        ( m ^ 2 )
                        =
                        (
                          n
                          x.
                          prod_ i e. ( 1 ... r ) ( a ` i )
                        )
                    )
                    ->
                    ( f ` n ) <_ ( a ` r )
                  )
            )
          )
        ->
        A. x e. ZZ
          A. y e. ZZ
            (
              (
                (
                  (
                    0 < x
                    /\
                    -. E. m e. ZZ ( m ^ 2 ) = x
                  )
                  /\
                  (
                    0 < y
                    /\
                    -. E. m e. ZZ ( m ^ 2 ) = y
                  )
                )
                /\
                ( f ` x ) = ( f ` y )
              )
              ->
              x = y
            )
      )
  $.
$}
