$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_b2: the maximum at zero among nonnegative real cosine
  polynomials whose coefficients at multiples of three vanish is 3, and the
  maximum is attained. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's RR ^m RR is the class of total real functions, and RR ^m NN0 is
  the class of real sequences indexed by the nonnegative integers. For a
  positive integer N, only the entries from 0 through N of the coefficient
  sequence are inspected, so this is equivalent to the source list of length
  N + 1. The finite sum from 1 through N is exactly the source cosine
  polynomial, while 3 || n expresses that n is a multiple of three.

  The first conjunct supplies an admissible polynomial attaining value 3 at
  zero. The second says that every admissible polynomial has value at zero at
  most 3. Together these are the source greatest-element assertion, including
  attainment. The final declaration is a single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d N a f n x $.

  putnambench-putnam-2013-b2 $a |- (
    E. N e. NN
      E. a e. ( RR ^m NN0 )
        E. f e. ( RR ^m RR )
          (
            (
              (
                A. x e. RR
                  (
                    ( f ` x )
                    =
                    (
                      1
                      +
                      sum_ n e. ( 1 ... N )
                        (
                          ( a ` n )
                          x.
                          (
                            cos
                            `
                            (
                              (
                                ( 2 x. _pi )
                                x.
                                n
                              )
                              x.
                              x
                            )
                          )
                        )
                    )
                  )
                /\
                A. x e. RR
                  0 <_ ( f ` x )
              )
              /\
              A. n e. ( 0 ... N )
                (
                  3 || n
                  ->
                  ( a ` n ) = 0
                )
            )
            /\
            ( f ` 0 ) = 3
          )
    /\
    A. N e. NN
      A. a e. ( RR ^m NN0 )
        A. f e. ( RR ^m RR )
          (
            (
              (
                A. x e. RR
                  (
                    ( f ` x )
                    =
                    (
                      1
                      +
                      sum_ n e. ( 1 ... N )
                        (
                          ( a ` n )
                          x.
                          (
                            cos
                            `
                            (
                              (
                                ( 2 x. _pi )
                                x.
                                n
                              )
                              x.
                              x
                            )
                          )
                        )
                    )
                  )
                /\
                A. x e. RR
                  0 <_ ( f ` x )
              )
              /\
              A. n e. ( 0 ... N )
                (
                  3 || n
                  ->
                  ( a ` n ) = 0
                )
            )
            ->
            ( f ` 0 ) <_ 3
          )
  ) $.
$}
