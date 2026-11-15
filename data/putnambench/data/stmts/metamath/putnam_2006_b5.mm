$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_b5: the maximum of the difference between two weighted
  unit-interval integrals over continuous real functions is 1/16.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions. Requiring its restriction
  to the closed unit interval to be a continuous map is exactly continuity
  on [0,1]. The S. binders are set.mm's real Lebesgue integrals; for these
  continuous integrands they agree with the source interval integrals.

  The first conjunct states that a continuous function attains 1/16 for
  I(F) - J(F), and the second states that every continuous function has
  value at most 1/16. Together these are exactly the source greatest-value
  assertion. The final declaration is a single unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

${
  $d F x $.

  putnambench-putnam-2006-b5 $a |- (
    E. F e. ( RR ^m RR )
      (
        ( F |` ( 0 [,] 1 ) ) e. ( ( 0 [,] 1 ) -cn-> RR )
        /\
        (
          (
            S. ( 0 [,] 1 )
              ( ( x ^ 2 ) x. ( F ` x ) )
              _d x
          )
          -
          (
            S. ( 0 [,] 1 )
              ( x x. ( ( F ` x ) ^ 2 ) )
              _d x
          )
        )
        =
        ( 1 / ; 1 6 )
      )
    /\
    A. F e. ( RR ^m RR )
      (
        ( F |` ( 0 [,] 1 ) ) e. ( ( 0 [,] 1 ) -cn-> RR )
        ->
        (
          (
            S. ( 0 [,] 1 )
              ( ( x ^ 2 ) x. ( F ` x ) )
              _d x
          )
          -
          (
            S. ( 0 [,] 1 )
              ( x x. ( ( F ` x ) ^ 2 ) )
              _d x
          )
        )
        <_
        ( 1 / ; 1 6 )
      )
  ) $.
$}
