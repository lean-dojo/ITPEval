$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_a2: the largest positive integer M(n) satisfying a binomial
  coefficient inequality has M(n) / n tending to (3 + sqrt(5)) / 2.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  M ranges over all nonnegative-integer-valued sequences. For each positive
  integer n, the antecedent says that M(n) is positive and satisfies

    ((M(n) - 1) choose n) < (M(n) choose (n - 1)),

  and that every positive integer m satisfying the same inequality is at
  most M(n). These two clauses are exactly the source IsGreatest condition.

  The value M(0) is unconstrained, as in the source formalizations, and does
  not affect the sequence limit. SetMM's _C is the binomial-coefficient
  operation, sqrt is the nonnegative real square root on 5, and ~~> is
  standard real-sequence convergence. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d M m n $.

  putnambench-putnam-2016-a2 $a |- A. M e. ( NN0 ^m NN0 )
    (
      (
        A. n e. NN
          (
            (
              (
                0 < ( M ` n )
                /\
                ( ( ( M ` n ) - 1 ) _C n )
                <
                ( ( M ` n ) _C ( n - 1 ) )
              )
              /\
              A. m e. NN
                (
                  (
                    ( ( m - 1 ) _C n )
                    <
                    ( m _C ( n - 1 ) )
                  )
                  ->
                  m <_ ( M ` n )
                )
            )
          )
      )
      ->
      (
        n e. NN0 |->
          (
            ( M ` n )
            /
            n
          )
      )
      ~~>
      (
        ( 3 + ( sqrt ` 5 ) )
        /
        2
      )
    )
  $.
$}
