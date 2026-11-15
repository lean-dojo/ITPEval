$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_b6: the threshold for the left-hand asymptotic behavior at
  one of the specified exponential power series is negative one half.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over arbitrary curried total functions from two real arguments
  to a real value. For every real a and every x in [0,1), the first
  antecedent identifies F(a,x) with the infinite real series from the source.
  Since n+1 is positive, set.mm's complex-power operation ^c agrees with the
  source real power (n+1)^a. Equality of the unbounded sum also asserts its
  convergence.

  The first limit clause is the epsilon-delta expansion of convergence to
  zero as x tends to one from below. The second says that every real bound is
  eventually a lower bound in the same left neighborhood, which is exactly
  convergence to positive infinity. The biconditional preserves the source
  characterization of c, with its annotated solution -1/2 made explicit.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d F a b c d e n x $.

  putnambench-putnam-2024-b6 $a |-
    A. F e. ( ( RR ^m RR ) ^m RR )
      A. c e. RR
        (
          A. a e. RR A. x e. RR
            (
              (
                0 <_ x
                /\
                x < 1
              )
              ->
              (
                (
                  sum_ n e. NN0
                    (
                      (
                        ( ( n + 1 ) ^c a )
                        x.
                        ( exp ` ( 2 x. ( n + 1 ) ) )
                      )
                      x.
                      ( x ^ ( ( n + 1 ) ^ 2 ) )
                    )
                )
                =
                ( ( F ` a ) ` x )
              )
            )
          ->
          (
            (
              (
                A. a e. RR
                  (
                    a < c
                    ->
                    A. e e. RR
                      (
                        0 < e
                        ->
                        E. d e. RR
                          (
                            0 < d
                            /\
                            A. x e. RR
                              (
                                (
                                  x < 1
                                  /\
                                  ( abs ` ( x - 1 ) ) < d
                                )
                                ->
                                (
                                  abs
                                  `
                                  (
                                    ( ( F ` a ) ` x )
                                    x.
                                    (
                                      exp
                                      `
                                      (
                                        -u
                                        (
                                          1
                                          /
                                          ( 1 - x )
                                        )
                                      )
                                    )
                                  )
                                )
                                < e
                              )
                          )
                      )
                  )
                /\
                A. a e. RR
                  (
                    c < a
                    ->
                    A. b e. RR
                      E. d e. RR
                        (
                          0 < d
                          /\
                          A. x e. RR
                            (
                              (
                                x < 1
                                /\
                                ( abs ` ( x - 1 ) ) < d
                              )
                              ->
                              b
                              <_
                              (
                                ( ( F ` a ) ` x )
                                x.
                                (
                                  exp
                                  `
                                  (
                                    -u
                                    (
                                      1
                                      /
                                      ( 1 - x )
                                    )
                                  )
                                )
                              )
                            )
                        )
                  )
              )
              <->
              c = ( ( -u 1 ) / 2 )
            )
          )
        )
  $.
$}
