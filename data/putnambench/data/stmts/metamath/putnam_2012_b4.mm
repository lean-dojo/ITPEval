$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_b4: finite-limit convergence of a logarithmically adjusted
  real sequence defined by an exponential recurrence. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over arbitrary real-valued sequences indexed by the nonnegative
  integers. The antecedent preserves the initial value A(0) = 1 and the
  recurrence A(n+1) = A(n) + exp(-A(n)) at every nonnegative index.

  The conclusion keeps the finite real limit internally existential. It uses
  the positive-index tail n |-> A(n) - log(n), where the natural logarithm is
  defined; deleting the single index zero does not change convergence at
  infinity. The Rocq source defines the solution proposition as True, in
  agreement with the Lean and Isabelle annotations, so the source
  biconditional is logically equivalent to the convergence assertion below.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A L n $.

  putnambench-putnam-2012-b4 $a |-
    A. A e. ( RR ^m NN0 )
      (
        (
          ( A ` 0 ) = 1
          /\
          A. n e. NN0
            ( A ` ( n + 1 ) )
            =
            (
              ( A ` n )
              +
              ( exp ` ( -u ( A ` n ) ) )
            )
        )
        ->
        E. L e. RR
          (
            n e. NN |->
              (
                ( A ` n )
                -
                ( log ` n )
              )
          )
          ~~>
          L
      )
  $.
$}
