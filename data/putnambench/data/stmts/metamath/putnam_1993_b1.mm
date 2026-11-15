$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_b1: the smallest positive integer denominator for which every
  integer m strictly between 0 and 1993 admits an integer k with k/n strictly
  between m/1993 and (m+1)/1994 is 3987. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ZZ are SetMM's classes of nonnegative integers and integers.
  The first conjunct says that 3987 satisfies the source predicate. The
  second says that 3987 is a lower bound for every nonnegative integer n
  satisfying it, which is the explicit attained-minimum expansion of the
  source IsLeast/LEAST statement.

  The quotients are real-valued SetMM divisions. Keeping k in ZZ matches the
  Lean and Isabelle statements; it is equivalent to Rocq's natural witness
  because the strict positive lower bound and positive n force k to be
  positive. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d k m n $.

  putnambench-putnam-1993-b1 $a |- (
    (
      0 < ( ; ; ; 3 9 8 7 )
      /\
      A. m e. ZZ
        (
          (
            0 < m
            /\
            m < ( ; ; ; 1 9 9 3 )
          )
          ->
          E. k e. ZZ
            (
              (
                m / ( ; ; ; 1 9 9 3 )
              )
              <
              (
                k / ( ; ; ; 3 9 8 7 )
              )
              /\
              (
                k / ( ; ; ; 3 9 8 7 )
              )
              <
              (
                ( m + 1 ) / ( ; ; ; 1 9 9 4 )
              )
            )
        )
    )
    /\
    A. n e. NN0
      (
        (
          0 < n
          /\
          A. m e. ZZ
            (
              (
                0 < m
                /\
                m < ( ; ; ; 1 9 9 3 )
              )
              ->
              E. k e. ZZ
                (
                  (
                    m / ( ; ; ; 1 9 9 3 )
                  )
                  <
                  (
                    k / n
                  )
                  /\
                  (
                    k / n
                  )
                  <
                  (
                    ( m + 1 ) / ( ; ; ; 1 9 9 4 )
                  )
                )
            )
        )
        ->
        ( ; ; ; 3 9 8 7 ) <_ n
      )
  ) $.
$}
