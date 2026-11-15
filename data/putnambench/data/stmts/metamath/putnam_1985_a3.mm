$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_a3: the diagonal limit of a family of real sequences defined
  by a quadratic recurrence is exp(d) - 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The function a ranges over all NN0-indexed families of NN0-indexed real
  sequences. The two antecedent conjuncts preserve the initial value
  a_m(0) = d / 2^m and the recurrence
  a_m(j+1) = a_m(j)^2 + 2 a_m(j) for every nonnegative m and j.

  The maps-to expression is the diagonal sequence n |-> a_n(n), and ~~> is
  set.mm's real-sequence convergence relation. Its target exp(d) - 1 is the
  explicit Rocq solution and the solution recorded in the Lean and Isabelle
  annotations. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a d j m n $.

  putnambench-putnam-1985-a3 $a |-
    A. d e. RR
    A. a e. ( ( RR ^m NN0 ) ^m NN0 )
      (
        (
          A. m e. NN0
            ( ( a ` m ) ` 0 ) = ( d / ( 2 ^ m ) )
          /\
          A. m e. NN0 A. j e. NN0
            ( ( a ` m ) ` ( j + 1 ) )
            =
            (
              ( ( ( a ` m ) ` j ) ^ 2 )
              +
              ( 2 x. ( ( a ` m ) ` j ) )
            )
        )
        ->
        (
          n e. NN0 |->
            ( ( a ` n ) ` n )
        )
        ~~>
        ( ( exp ` d ) - 1 )
      )
  $.
$}
