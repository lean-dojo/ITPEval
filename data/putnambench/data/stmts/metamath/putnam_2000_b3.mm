$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_b3: monotonicity and limiting value of the total zero
  multiplicities of the iterated derivatives of a finite real sine
  polynomial. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The coefficient function has exact domain 1 ... N, matching the Lean
  subtype; extending it arbitrarily outside that interval gives the
  equivalent total sequence used by Isabelle. P00B3Deriv is the total real
  derivative, with value zero where set.mm's partial derivative is undefined.
  IterComp therefore matches Lean's total iteratedDeriv, including order zero.

  The multiplicity hypothesis says that whenever some iterated derivative is
  nonzero, U(g)(t) is nonzero at that order and every smaller order vanishes.
  Over NN0 this is equivalent to Isabelle's least-order definition. The
  arbitrary-index nonnegative sum is indexed by the real half-open interval
  0 [,) 1, exactly matching the source subtype/index set. It is the supremum
  of all finite subsums when those subsums have a natural upper bound, and is
  zero otherwise. For NN0-valued families this is exactly the totalized
  infinite sum used by Lean and Isabelle. Since M is NN0-valued, set.mm
  sequence convergence to 2 x. N is equivalent to convergence in the discrete
  topology on NN0 used by the sources.

  The final declaration is the single unproved $a corpus statement. This
  extension file introduces no $p proof statement; the included set.mm
  library retains its existing verified proofs.
$)

$c P00B3Deriv P00B3IterDeriv P00B3FiniteSums P00B3NNSum $.

p00b3-deriv-syntax $a class P00B3Deriv $.
p00b3-iter-deriv-syntax $a class ( P00B3IterDeriv n A ) $.
p00b3-finite-sums-syntax $a class ( P00B3FiniteSums I H ) $.
p00b3-nnsum-syntax $a class ( P00B3NNSum I H ) $.

${
  $d A x $.

  p00b3-deriv-definition $a |- P00B3Deriv =
    (
      A e. ( RR ^m RR ) |->
        (
          x e. RR |->
            if (
              x e. dom ( RR _D A ) ,
              ( ( RR _D A ) ` x ) ,
              0
            )
        )
    ) $.
$}

p00b3-iter-deriv-definition $a |- ( P00B3IterDeriv n A ) =
  (
    ( ( IterComp ` P00B3Deriv ) ` n )
    `
    A
  ) $.

${
  $d H I s t z $.

  p00b3-finite-sums-definition $a |- ( P00B3FiniteSums I H ) =
    {
      z e. NN0 |
        E. s e. ( ~P I i^i Fin )
          z = sum_ t e. s ( H ` t )
    } $.
$}

${
  $d H I b z $.

  p00b3-nnsum-definition $a |- ( P00B3NNSum I H ) =
    if (
      E. b e. NN0
        A. z e. ( P00B3FiniteSums I H )
          z <_ b ,
      sup ( ( P00B3FiniteSums I H ) , NN0 , < ) ,
      0
    ) $.
$}

${
  $d A F M N U c g i j k t $.

  putnambench-putnam-2000-b3 $a |-
    A. N e. NN0
    A. A e. ( RR ^m ( 1 ... N ) )
    A. F e. ( RR ^m RR )
    A. U e. ( ( NN0 ^m RR ) ^m ( RR ^m RR ) )
    A. M e. ( NN0 ^m NN0 )
      (
        (
          (
            (
              (
                0 < N
                /\
                ( A ` N ) =/= 0
              )
              /\
              F =
                (
                  t e. RR |->
                    sum_ j e. ( 1 ... N )
                      (
                        ( A ` j )
                        x.
                        (
                          sin
                          `
                          (
                            (
                              ( 2 x. _pi )
                              x.
                              j
                            )
                            x.
                            t
                          )
                        )
                      )
                )
            )
            /\
            A. g e. ( RR ^m RR ) A. t e. RR
              (
                E. c e. NN0
                  ( ( P00B3IterDeriv c g ) ` t ) =/= 0
                ->
                (
                  (
                    (
                      P00B3IterDeriv
                        ( ( U ` g ) ` t )
                        g
                    )
                    `
                    t
                  )
                  =/= 0
                  /\
                  A. k e. NN0
                    (
                      k < ( ( U ` g ) ` t )
                      ->
                      ( ( P00B3IterDeriv k g ) ` t ) = 0
                    )
                )
              )
          )
          /\
          A. k e. NN0
            ( M ` k )
            =
            ( P00B3NNSum
              ( 0 [,) 1 )
              (
                t e. ( 0 [,) 1 ) |->
                  (
                    (
                      U
                      `
                      ( P00B3IterDeriv k F )
                    )
                    `
                    t
                  )
              )
            )
        )
        ->
        (
          A. i e. NN0 A. j e. NN0
            (
              i <_ j
              ->
              ( M ` i ) <_ ( M ` j )
            )
          /\
          M ~~> ( 2 x. N )
        )
      )
  $.
$}
