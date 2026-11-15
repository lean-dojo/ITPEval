$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_b1: the recursively defined real sequence beginning at one,
  with each next term the natural logarithm of exp(x_n) - x_n, has
  convergent infinite sum exp(1) - 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is set.mm's class of all real-valued sequences indexed by the
  nonnegative integers. The antecedent preserves the initial value and the
  recurrence at every such index. For real t, exp(t) - t is positive, so
  set.mm's logarithm here agrees with the real natural logarithm in the
  source statement.

  The unbounded sum_ is set.mm's infinite-series sum: a divergent series
  evaluates to the empty set, so equality to the displayed real value also
  states convergence. The right side is the published answer exp(1) - 1,
  annotated in the Lean and Isabelle sources. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d n x $.

  putnambench-putnam-2016-b1 $a |-
    A. x e. ( RR ^m NN0 )
      (
        (
          ( x ` 0 ) = 1
          /\
          A. n e. NN0
            (
              ( x ` ( n + 1 ) )
              =
              (
                log
                `
                (
                  ( exp ` ( x ` n ) )
                  -
                  ( x ` n )
                )
              )
            )
        )
        ->
        (
          sum_ n e. NN0
            ( x ` n )
        )
        =
        ( ( exp ` 1 ) - 1 )
      )
  $.
$}
