$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_b6: a Lipschitz real function on the unit interval whose
  rational values are integral-affine is affine on each member of a finite
  interval cover of the unit interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions. The first hypothesis keeps
  the positive Lipschitz constant existentially quantified and restricts both
  real arguments to the closed unit interval. The second ranges over every
  rational in that interval and keeps its two integer witnesses internal.

  A positive integer n and four real-valued functions on 1 ... n encode the
  finite family of closed intervals, their slopes, and their intercepts.
  Every endpoint pair is ordered, F is affine throughout its corresponding
  interval, and the indexed union is exactly [0,1]. Since a cover of [0,1]
  is nonempty, positive finite indexing is bidirectionally equivalent to the
  source finite-family formulation. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A B C F K M a b i n r x y $.

  putnambench-putnam-2014-b6 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          E. K e. RR
            (
              0 < K
              /\
              A. x e. ( 0 [,] 1 )
                A. y e. ( 0 [,] 1 )
                  (
                    abs ` ( ( F ` x ) - ( F ` y ) )
                  )
                  <_
                  (
                    K x. ( abs ` ( x - y ) )
                  )
            )
          /\
          A. r e. QQ
            (
              r e. ( 0 [,] 1 )
              ->
              E. a e. ZZ
                E. b e. ZZ
                  (
                    ( F ` r )
                    =
                    ( a + ( b x. r ) )
                  )
            )
        )
        ->
        E. n e. NN
          E. A e. ( RR ^m ( 1 ... n ) )
            E. B e. ( RR ^m ( 1 ... n ) )
              E. M e. ( RR ^m ( 1 ... n ) )
                E. C e. ( RR ^m ( 1 ... n ) )
                  (
                    A. i e. ( 1 ... n )
                      (
                        ( A ` i ) <_ ( B ` i )
                        /\
                        A. x e.
                          ( ( A ` i ) [,] ( B ` i ) )
                            (
                              ( F ` x )
                              =
                              (
                                ( C ` i )
                                +
                                ( ( M ` i ) x. x )
                              )
                            )
                      )
                    /\
                    (
                      ( 0 [,] 1 )
                      =
                      U_ i e. ( 1 ... n )
                        ( ( A ` i ) [,] ( B ` i ) )
                    )
                  )
      )
  $.
$}
