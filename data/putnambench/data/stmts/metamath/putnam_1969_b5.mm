$(
  Statement-only formalization of PutnamBench artifact putnam_1969_b5:
  a positive strictly increasing integer sequence with convergent reciprocal
  series has a counting function whose ratio to its real threshold tends to
  zero at positive infinity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is a positive-integer sequence indexed by NN0, and K is its counting
  function on real thresholds. The first quantified premise states strict
  increase; positivity follows from the codomain. The second expands
  convergence of the reciprocal partial sums,
  using the half-open interval 0 ..^ n for the first n terms. The cardinality
  equation defines K(x) as the number of indices whose sequence values do not
  exceed x; equality to the natural number K(x) also records finiteness.

  The conclusion is the epsilon-threshold expansion of K(t) / t tending to
  zero as the real variable t tends to positive infinity. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d A C K M N e i m n t x $.

  putnambench-putnam-1969-b5 $a |- A. A A. K
    (
      (
        (
          (
            A : NN0 --> NN
            /\
            K : RR --> NN0
          )
          /\
          (
            A. n e. NN0 0 < ( A ` n )
            /\
            A. m e. NN0
              A. n e. NN0
                (
                  m < n
                  ->
                  ( A ` m ) < ( A ` n )
                )
          )
        )
        /\
        (
          E. C e. RR
            A. e e. RR
              (
                0 < e
                ->
                E. N e. NN0
                  A. n e. NN0
                    (
                      N <_ n
                      ->
                      (
                        abs
                        `
                        (
                          (
                            sum_ i e. ( 0 ..^ n )
                              ( 1 / ( A ` i ) )
                          )
                          -
                          C
                        )
                      )
                      < e
                    )
              )
          /\
          A. x e. RR
            (
              ( K ` x )
              =
              (
                #
                `
                { n e. NN0 | ( A ` n ) <_ x }
              )
            )
        )
      )
      ->
      A. e e. RR
        (
          0 < e
          ->
          E. M e. RR
            A. t e. RR
              (
                M <_ t
                ->
                (
                  abs
                  `
                  (
                    (
                      ( K ` t )
                      /
                      t
                    )
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
