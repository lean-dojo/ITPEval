$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_a3: characterization of the initial real values for which a
  nonzero recurrence sequence takes integer values infinitely often.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  f ranges over all total real-valued sequences indexed by the nonnegative
  integers. The first premise preserves nonvanishing at every index and the
  recurrence at every n at least 3. The left side of the biconditional keeps
  the source's unbounded-index formulation of infinitely many integer-valued
  terms. The right side is the explicit solution predicate from the sources:
  the first two terms are one and the same integer.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a f m n $.

  putnambench-putnam-1979-a3 $a |-
    A. f e. ( RR ^m NN0 )
      (
        A. n e. NN0
          (
            ( f ` n ) =/= 0
            /\
            (
              3 <_ n
              ->
              ( f ` n )
              =
              (
                (
                  ( f ` ( n - 2 ) )
                  x.
                  ( f ` ( n - 1 ) )
                )
                /
                (
                  (
                    2
                    x.
                    ( f ` ( n - 2 ) )
                  )
                  -
                  ( f ` ( n - 1 ) )
                )
              )
            )
          )
        ->
        (
          (
            A. m e. NN0
              E. n e. NN0
                (
                  m < n
                  /\
                  E. a e. ZZ
                    ( f ` n ) = a
                )
          )
          <->
          E. a e. ZZ
            (
              ( f ` 1 ) = a
              /\
              ( f ` 2 ) = a
            )
        )
      )
  $.
$}
