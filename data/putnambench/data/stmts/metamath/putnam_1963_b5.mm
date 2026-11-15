$(
  Statement-only formalization of PutnamBench artifact putnam_1963_b5:
  convergence to zero of n times the nth term of a convergent real series
  whose terms satisfy a dyadic-interval comparison bound. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A is an integer-indexed real sequence. The first conjunct is the source
  inequality for all integer n >= 1 and n <= k <= 2n. The second conjunct
  expands convergence of the nonnegative-index partial sums to an
  existential real limit S. The conclusion expands convergence of n A(n) to
  zero at positive infinity on the integers. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d A S e k m n N $.

  putnambench-putnam-1963-b5 $a |- A. A e. ( RR ^m ZZ )
    (
      (
        A. n e. ZZ
          (
            1 <_ n
            ->
            A. k e. ZZ
              (
                (
                  n <_ k
                  /\
                  k <_ ( 2 x. n )
                )
                ->
                (
                  0 <_ ( A ` k )
                  /\
                  ( A ` k )
                  <_
                  (
                    ( ( 9 + 1 ) x. ( 9 + 1 ) )
                    x.
                    ( A ` n )
                  )
                )
              )
          )
        /\
        E. S e. RR
          A. e e. RR
            (
              0 < e
              ->
              E. m e. NN0
                A. N e. NN0
                  (
                    m <_ N
                    ->
                    (
                      abs
                      `
                      (
                        (
                          sum_ k e. ( 0 ..^ N )
                            ( A ` k )
                        )
                        -
                        S
                      )
                    )
                    < e
                  )
            )
      )
      ->
      A. e e. RR
        (
          0 < e
          ->
          E. m e. ZZ
            A. n e. ZZ
              (
                m <_ n
                ->
                (
                  abs
                  `
                  (
                    ( n x. ( A ` n ) )
                    -
                    0
                  )
                )
                < e
              )
        )
    )
  $.
$}
