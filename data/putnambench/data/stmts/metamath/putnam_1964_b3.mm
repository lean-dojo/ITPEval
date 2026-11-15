$(
  Statement-only formalization of PutnamBench artifact putnam_1964_b3:
  a continuous real function that tends to zero along every positive
  arithmetic ray n alpha also tends to zero at positive infinity. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over total real functions. Membership in ( RR -cn-> RR ) is the
  native set.mm assertion of continuity. The first epsilon-threshold formula
  expands convergence of F(n alpha) to zero for every positive real alpha as
  n tends to infinity through NN0. The conclusion similarly expands
  convergence of F(x) to zero as the real variable x tends to positive
  infinity. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d F M N a e n x $.

  putnambench-putnam-1964-b3 $a |- A. F e. ( RR ^m RR )
    (
      (
        F e. ( RR -cn-> RR )
        /\
        A. a e. RR
          (
            0 < a
            ->
            A. e e. RR
              (
                0 < e
                ->
                E. N e. NN0
                  A. n e. NN0
                    (
                      N <_ n
                      ->
                      ( abs ` ( F ` ( n x. a ) ) ) < e
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
            A. x e. RR
              (
                M <_ x
                ->
                ( abs ` ( F ` x ) ) < e
              )
        )
    )
  $.
$}
