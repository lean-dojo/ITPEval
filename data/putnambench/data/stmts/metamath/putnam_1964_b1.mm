$(
  Statement-only formalization of PutnamBench artifact putnam_1964_b1:
  convergence to zero of the ratio between a positive integer sequence's
  counting function and its threshold. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is a positive-integer-valued sequence indexed by NN0. For each n, B(n)
  is the number of indices k for which A(k) <= n; equality with a value of B
  also records that this set is finite, since set.mm assigns +oo to the size
  of an infinite set.

  The first hypothesis expands convergence of the reciprocal series into
  epsilon-threshold convergence of its real partial sums. The conclusion
  similarly expands convergence of B(n) / n to zero. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof statement.
$)

${
  $d A B L e i k m n $.

  putnambench-putnam-1964-b1 $a |- A. A e. ( NN ^m NN0 )
    A. B e. ( NN0 ^m NN0 )
      (
        (
          E. L e. RR
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
                          L
                        )
                      )
                      < e
                    )
              )
          /\
          A. n e. NN0
            (
              ( B ` n )
              =
              (
                #
                `
                { k e. NN0 | ( A ` k ) <_ n }
              )
            )
        )
        ->
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
                        ( B ` n )
                        /
                        n
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
