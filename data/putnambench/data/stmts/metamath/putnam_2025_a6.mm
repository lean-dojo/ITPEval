$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_a6 (putnambench__metamath__putnam_2025_a6): exact
  divisibility by powers of two in the recursively defined integer
  sequence b. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ ^m NN0 is SetMM's class of integer-valued sequences indexed by the
  nonnegative integers. The antecedent gives exactly b(0) = 0 and the
  successor recursion b(n+1) = 2 b(n)^2 + b(n) + 1. Since this recursion
  uniquely determines the sequence, universal quantification over sequences
  satisfying it is equivalent to the fixed recursive definition in the Lean
  source.

  SetMM's positive integers NN encode the source hypothesis 1 <= k. The two
  conjuncts state that 2^(2k+2) divides the indicated integer difference and
  that 2^(2k+3) does not. The final declaration is the single unproved $a
  corpus statement; this artifact file adds no $p proof declaration.
$)

${
  $d B k n $.

  putnambench-putnam-2025-a6 $a |-
    A. B e. ( ZZ ^m NN0 )
      (
        (
          ( B ` 0 ) = 0
          /\
          A. n e. NN0
            ( B ` ( n + 1 ) )
            =
            (
              (
                2
                x.
                ( ( B ` n ) ^ 2 )
              )
              +
              (
                ( B ` n )
                +
                1
              )
            )
        )
        ->
        A. k e. NN
          (
            (
              2
              ^
              (
                ( 2 x. k )
                +
                2
              )
            )
            ||
            (
              ( B ` ( 2 ^ ( k + 1 ) ) )
              -
              (
                2
                x.
                ( B ` ( 2 ^ k ) )
              )
            )
            /\
            -.
            (
              (
                2
                ^
                (
                  ( 2 x. k )
                  +
                  3
                )
              )
              ||
              (
                ( B ` ( 2 ^ ( k + 1 ) ) )
                -
                (
                  2
                  x.
                  ( B ` ( 2 ^ k ) )
                )
              )
            )
          )
      )
  $.
$}
