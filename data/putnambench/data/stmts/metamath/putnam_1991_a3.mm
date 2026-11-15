$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_a3: classification of real polynomials whose distinct ordered
  roots have derivative zeros at every adjacent midpoint. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A in RR ^m NN0 is the complete coefficient function of a real polynomial.
  The antecedent says that n is its exact degree: the coefficient at n is
  nonzero and every later coefficient vanishes. Evaluation is the finite sum
  through n, and the sum from 1 through n is the formal derivative evaluated
  at the indicated point.

  R is an arbitrary NN0-indexed real sequence. The half-open ranges 0 ..^ n
  and 0 ..^ (n - 1) are the zero-based versions of the source root and
  adjacent-pair index scopes. The right side inlines the common documented
  solution set: degree two with two distinct real roots. Hence the
  coefficient-function representation is bidirectionally equivalent to the
  source statement about real polynomials. The final declaration is a single
  unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d A R i k n x y $.

  putnambench-putnam-1991-a3 $a |-
    A. A e. ( RR ^m NN0 )
      A. n e. NN0
        (
          (
            (
              ( A ` n ) =/= 0
              /\
              A. k e. NN0
                (
                  n < k
                  ->
                  ( A ` k ) = 0
                )
            )
            /\
            2 <_ n
          )
          ->
          (
            E. R e. ( RR ^m NN0 )
              (
                A. i e. ( 0 ..^ ( n - 1 ) )
                  ( R ` i ) < ( R ` ( i + 1 ) )
                /\
                (
                  A. i e. ( 0 ..^ n )
                    (
                      sum_ k e. ( 0 ... n )
                        (
                          ( A ` k )
                          x.
                          ( ( R ` i ) ^ k )
                        )
                    )
                    =
                    0
                  /\
                  A. i e. ( 0 ..^ ( n - 1 ) )
                    (
                      sum_ k e. ( 1 ... n )
                        (
                          (
                            k
                            x.
                            ( A ` k )
                          )
                          x.
                          (
                            (
                              (
                                ( R ` i )
                                +
                                ( R ` ( i + 1 ) )
                              )
                              /
                              2
                            )
                            ^
                            ( k - 1 )
                          )
                        )
                    )
                    =
                    0
                )
              )
            <->
            (
              n = 2
              /\
              E. x e. RR
                E. y e. RR
                  (
                    x =/= y
                    /\
                    (
                      (
                        sum_ k e. ( 0 ... n )
                          (
                            ( A ` k )
                            x.
                            ( x ^ k )
                          )
                      )
                      =
                      0
                      /\
                      (
                        sum_ k e. ( 0 ... n )
                          (
                            ( A ` k )
                            x.
                            ( y ^ k )
                          )
                      )
                      =
                      0
                    )
                  )
            )
          )
        )
  $.
$}
