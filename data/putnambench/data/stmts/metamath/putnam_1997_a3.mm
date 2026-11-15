$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_a3: evaluation of the improper real integral of the product of
  two factorial-denominator power series as sqrt(exp(1)). This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  f and g are arbitrary total real functions constrained to be the two
  source power series. The half-open index set 0 ..^ n is {0,...,n-1}, so
  the finite products are respectively 2 * 4 * ... * (2n) and its
  termwise square, including the empty product at n = 0.

  The sum over NN0 is set.mm's convergent infinite real-series sum, and S.
  is its real Lebesgue integral. The epsilon-threshold conclusion is the
  real at-positive-infinity limit of the integrals over [0,t]. Its target is
  the explicit Rocq solution and the value recorded in the Lean and Isabelle
  annotations. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d e f g i m n t x $.

  putnambench-putnam-1997-a3 $a |-
    A. f e. ( RR ^m RR )
    A. g e. ( RR ^m RR )
      (
        (
          f
          =
          (
            x e. RR |->
              sum_ n e. NN0
                (
                  (
                    ( ( -u 1 ) ^ n )
                    x.
                    ( x ^ ( ( 2 x. n ) + 1 ) )
                  )
                  /
                  (
                    prod_ i e. ( 0 ..^ n )
                      ( 2 x. ( i + 1 ) )
                  )
                )
          )
          /\
          g
          =
          (
            x e. RR |->
              sum_ n e. NN0
                (
                  ( x ^ ( 2 x. n ) )
                  /
                  (
                    prod_ i e. ( 0 ..^ n )
                      ( ( 2 x. ( i + 1 ) ) ^ 2 )
                  )
                )
          )
        )
        ->
        A. e e. RR
          (
            0 < e
            ->
            E. m e. RR
              A. t e. RR
                (
                  m <_ t
                  ->
                  (
                    abs
                    `
                    (
                      (
                        S. ( 0 [,] t )
                          ( ( f ` x ) x. ( g ` x ) )
                          _d x
                      )
                      -
                      ( sqrt ` ( exp ` 1 ) )
                    )
                  )
                  <
                  e
                )
          )
      )
  $.
$}
