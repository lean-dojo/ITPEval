$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_a5: the greatest integer having exactly 2020 representations
  as a sum of distinct positive-index Fibonacci numbers is the Fibonacci
  number F(4040) minus one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over total NN0-valued sequences on NN0. Its two initial values
  and recurrence are exactly Nat.fib from the Lean source. The restricted
  class abstraction contains precisely the finite subsets S of the positive
  integers whose Fibonacci values sum to the displayed integer, and # is
  their finite cardinality.

  The source function a is eliminated by its defining equality. The final
  conjunction expands IsGreatest: the annotated solution F(4040) - 1 has
  count 2020, and every integer with count 2020 is at most that solution.
  The universal conditional over F is equivalent because the initial values
  and recurrence uniquely determine the Fibonacci sequence. The declaration
  below is an unproved $a statement encoding; there is no $p proof.
$)

${
  $d F S k n $.

  putnambench-putnam-2020-a5 $a |-
    A. F e. ( NN0 ^m NN0 )
      (
        (
          (
            ( F ` 0 ) = 0
            /\
            ( F ` 1 ) = 1
          )
          /\
          A. n e. NN0
            (
              F
              `
              ( n + 2 )
            )
            =
            (
              ( F ` ( n + 1 ) )
              +
              ( F ` n )
            )
        )
        ->
        (
          (
            #
            `
            {
              S e. Fin |
              (
                S C_ NN
                /\
                (
                  sum_ k e. S ( F ` k )
                )
                =
                (
                  ( F ` ; ; ; 4 0 4 0 )
                  -
                  1
                )
              )
            }
          )
          =
          ; ; ; 2 0 2 0
          /\
          A. n e. ZZ
            (
              (
                #
                `
                {
                  S e. Fin |
                  (
                    S C_ NN
                    /\
                    (
                      sum_ k e. S ( F ` k )
                    )
                    =
                    n
                  )
                }
              )
              =
              ; ; ; 2 0 2 0
              ->
              n
              <_
              (
                ( F ` ; ; ; 4 0 4 0 )
                -
                1
              )
            )
        )
      )
  $.
$}
