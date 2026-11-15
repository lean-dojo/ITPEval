$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_b5: evaluation of the left-hand limit at one of an infinite
  product with real exponents as two divided by exp(1). This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over arbitrary real-valued functions. For each real x in the open
  unit interval, its value is assumed to be the limit of the finite products
  indexed by 0 ..^ N, namely the indices 0 through N - 1. This is exactly the
  exclusive partial-product convention of the Lean and Rocq sources; the
  inclusive Isabelle convention is the same sequence with an index shift.

  Every ratio base is positive on 0 < x < 1, so set.mm's complex-power
  operation ^c agrees with the source real power
  exp((x^n) log((1+x^(n+1))/(1+x^n))). The relation ~~> is standard
  sequence convergence. The conclusion expands the left-hand limit at one
  into its epsilon-delta definition and uses the explicit solution 2/exp(1).

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d F N d e n x $.

  putnambench-putnam-2004-b5 $a |- A. F e. ( RR ^m RR )
    (
      (
        A. x e. RR
          (
            (
              0 < x
              /\
              x < 1
            )
            ->
            (
              (
                N e. NN0 |->
                  prod_ n e. ( 0 ..^ N )
                    (
                      (
                        (
                          1
                          +
                          ( x ^ ( n + 1 ) )
                        )
                        /
                        (
                          1
                          +
                          ( x ^ n )
                        )
                      )
                      ^c
                      ( x ^ n )
                    )
              )
              ~~>
              ( F ` x )
            )
          )
      )
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
                      ( F ` x )
                      -
                      ( 2 / ( exp ` 1 ) )
                    )
                  )
                  < e
                )
            )
        )
    )
  $.
$}
