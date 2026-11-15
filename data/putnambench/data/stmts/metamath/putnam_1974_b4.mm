$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1974_b4: every real-valued function on the real plane that is
  continuous separately in each coordinate is a pointwise limit of a sequence
  of jointly continuous real-valued functions on the plane. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total functions from RR X. RR to RR. The two antecedent
  clauses expand continuity of each one-variable section in epsilon-delta
  form.

  G is internally existentially quantified as an NN0-indexed sequence of total
  real-valued functions on RR X. RR. Coordinatewise delta-neighborhoods give
  the standard product topology on the real plane, so the first conclusion
  conjunct is exactly joint continuity of every G(n). The second conjunct is
  pointwise convergence to F in epsilon-threshold form.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F G N d e n u v x y $.

  putnambench-putnam-1974-b4 $a
    |- A. F e. ( RR ^m ( RR X. RR ) )
      (
        (
          A. y e. RR A. x e. RR A. e e. RR
            (
              0 < e
              ->
              E. d e. RR
                (
                  0 < d
                  /\
                  A. u e. RR
                    (
                      ( abs ` ( u - x ) ) < d
                      ->
                      (
                        abs
                        `
                        (
                          ( F ` <. u , y >. )
                          -
                          ( F ` <. x , y >. )
                        )
                      )
                      < e
                    )
                )
          /\
          A. x e. RR A. y e. RR A. e e. RR
            (
              0 < e
              ->
              E. d e. RR
                (
                  0 < d
                  /\
                  A. v e. RR
                    (
                      ( abs ` ( v - y ) ) < d
                      ->
                      (
                        abs
                        `
                        (
                          ( F ` <. x , v >. )
                          -
                          ( F ` <. x , y >. )
                        )
                      )
                      < e
                    )
                )
        )
        ->
        E. G e. ( ( RR ^m ( RR X. RR ) ) ^m NN0 )
          (
            A. n e. NN0 A. x e. RR A. y e. RR A. e e. RR
              (
                0 < e
                ->
                E. d e. RR
                  (
                    0 < d
                    /\
                    A. u e. RR A. v e. RR
                      (
                        (
                          ( abs ` ( u - x ) ) < d
                          /\
                          ( abs ` ( v - y ) ) < d
                        )
                        ->
                        (
                          abs
                          `
                          (
                            ( ( G ` n ) ` <. u , v >. )
                            -
                            ( ( G ` n ) ` <. x , y >. )
                          )
                        )
                        < e
                      )
                  )
            /\
            A. x e. RR A. y e. RR A. e e. RR
              (
                0 < e
                ->
                E. N e. NN0 A. n e. NN0
                  (
                    N <_ n
                    ->
                    (
                      abs
                      `
                      (
                        ( ( G ` n ) ` <. x , y >. )
                        -
                        ( F ` <. x , y >. )
                      )
                    )
                    < e
                  )
              )
          )
      )
  $.
$}
