$(
  Statement-only formalization of PutnamBench artifact putnam_1964_a5:
  existence of a universal real constant bounding the series of reciprocals
  of positive-sequence prefix averages by the convergent reciprocal series.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is the class of real sequences indexed by the nonnegative
  integers. For n in NN0, 0 ..^ n indexes the first n terms. Each convergence
  assertion below is expanded in epsilon-threshold form.

  The hypothesis says that A is positive and its reciprocal partial sums
  converge. The conclusion supplies limits B and C for the prefix-average
  series and reciprocal series, respectively, and asserts B <= K C. This
  directly expands the source predicate pa and preserves the internally
  quantified series limits. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d A B C K e i j m n $.

  putnambench-putnam-1964-a5 $a |- E. K e. RR
    A. A e. ( RR ^m NN0 )
      (
        (
          A. i e. NN0 0 < ( A ` i )
          /\
          E. C e. RR
            A. e e. RR
              (
                0 < e
                ->
                E. m e. NN0
                  A. n e. NN0
                    (
                      m <_ n
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
        )
        ->
        E. B e. RR E. C e. RR
          (
            A. e e. RR
              (
                0 < e
                ->
                E. m e. NN0
                  A. n e. NN0
                    (
                      m <_ n
                      ->
                      (
                        abs
                        `
                        (
                          (
                            sum_ i e. ( 0 ..^ n )
                              (
                                ( i + 1 )
                                /
                                (
                                  sum_ j e. ( 0 ..^ ( i + 1 ) )
                                    ( A ` j )
                                )
                              )
                          )
                          -
                          B
                        )
                      )
                      < e
                    )
              )
            /\
            (
              A. e e. RR
                (
                  0 < e
                  ->
                  E. m e. NN0
                    A. n e. NN0
                      (
                        m <_ n
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
              B <_ ( K x. C )
            )
          )
      )
  $.
$}
