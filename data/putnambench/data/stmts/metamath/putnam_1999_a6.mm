$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_a6: every real sequence with initial values 1, 2, and 24 and
  the specified rational recurrence has each positive-indexed term equal to
  an integer multiple of its index. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over every real-valued sequence indexed by the nonnegative
  integers. The recurrence is imposed exactly at the natural indices n >= 4,
  and uses set.mm's real arithmetic and division. The conclusion retains the
  existential integer multiplier inside the universal positive-index
  quantifier.

  Lean declares A on all integers, but its assumptions and conclusion only
  apply A to nonnegative indices. Restriction to NN0 and arbitrary extension
  back to ZZ therefore give a bidirectional equivalence with that formulation.
  The Rocq source presents the same sequence with zero-based indexing, so its
  A(n) = (n+1)k conclusion corresponds to the one-based Isabelle and Lean
  formulation used here. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d A k n $.

  putnambench-putnam-1999-a6 $a |- A. A e. ( RR ^m NN0 )
    (
      (
        (
          (
            ( A ` 1 ) = 1
            /\
            ( A ` 2 ) = 2
          )
          /\
          ( A ` 3 ) = ; 2 4
        )
        /\
        A. n e. NN
          (
            4 <_ n
            ->
            ( A ` n )
            =
            (
              (
                (
                  (
                    6
                    x.
                    ( ( A ` ( n - 1 ) ) ^ 2 )
                  )
                  x.
                  ( A ` ( n - 3 ) )
                )
                -
                (
                  (
                    8
                    x.
                    ( A ` ( n - 1 ) )
                  )
                  x.
                  ( ( A ` ( n - 2 ) ) ^ 2 )
                )
              )
              /
              (
                ( A ` ( n - 2 ) )
                x.
                ( A ` ( n - 3 ) )
              )
            )
          )
      )
      ->
      A. n e. NN
        E. k e. ZZ
          ( A ` n ) = ( k x. n )
    )
  $.
$}
