$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_a1: the power series of exp(a x) cos(b x), for positive real
  a and b, has either no zero coefficients or infinitely many zero
  coefficients. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P ranges over all real-valued sequences indexed by NN0. The source
  definitions of f(x) = exp(a x) cos(b x) and of the zero-coefficient set
  are inlined. The epsilon-N premise states convergence, at every real x in
  an open ball about zero, of the partial sums indexed by 0 ..^ m to f(x).
  This is bidirectionally equivalent to the source power-series identity:
  convergence gives the infinite-sum equality, while any source neighborhood
  may be shrunk around zero so that exp(a x) cos(b x) is nonzero and its
  infinite-sum equality forces convergence. The conclusion says that the
  zero-coefficient set is empty or is not a member of Fin.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P N a b c e m n x $.

  putnambench-putnam-1970-a1 $a |-
    A. a e. RR
      A. b e. RR
        A. P e. ( RR ^m NN0 )
          (
            (
              (
                0 < a
                /\
                0 < b
              )
              /\
              E. c e. RR
                (
                  0 < c
                  /\
                  A. x e. RR
                    (
                      ( abs ` x ) < c
                      ->
                      A. e e. RR
                        (
                          0 < e
                          ->
                          E. N e. NN0
                            A. m e. NN0
                              (
                                N <_ m
                                ->
                                (
                                  abs
                                  `
                                  (
                                    (
                                      sum_ n e. ( 0 ..^ m )
                                        (
                                          ( P ` n )
                                          x.
                                          ( x ^ n )
                                        )
                                    )
                                    -
                                    (
                                      ( exp ` ( a x. x ) )
                                      x.
                                      ( cos ` ( b x. x ) )
                                    )
                                  )
                                )
                                < e
                              )
                        )
                    )
                )
            )
            ->
            (
              { n e. NN0 | ( P ` n ) = 0 } = (/)
              \/
              { n e. NN0 | ( P ` n ) = 0 } e/ Fin
            )
          )
  $.
$}
