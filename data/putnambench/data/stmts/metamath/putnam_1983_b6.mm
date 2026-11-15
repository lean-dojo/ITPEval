$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_b6: for every positive integer n and nontrivial complex
  (2^n + 1)-st root of unity, two integer-coefficient polynomials have
  squared values summing to -1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P and Q are complete integer-valued coefficient functions on NN0. The
  internally existential bounds d and e require the respective coefficient
  functions to vanish above those bounds, so they represent exactly arbitrary
  polynomials over ZZ, including the zero polynomial. The finite sums are
  their evaluations at the complex number a. This finite-support coefficient
  encoding is bidirectionally equivalent to the polynomial objects in the
  Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P Q a d e k n $.

  putnambench-putnam-1983-b6 $a |-
    A. n e. NN
      A. a e. CC
        (
          (
            (
              ( a ^ ( ( 2 ^ n ) + 1 ) )
              -
              1
            )
            =
            0
            /\
            a =/= 1
          )
          ->
          E. P e. ( ZZ ^m NN0 )
            E. Q e. ( ZZ ^m NN0 )
              E. d e. NN0
                E. e e. NN0
                  (
                    (
                      A. k e. NN0
                        ( d < k -> ( P ` k ) = 0 )
                      /\
                      A. k e. NN0
                        ( e < k -> ( Q ` k ) = 0 )
                    )
                    /\
                    (
                      (
                        sum_ k e. ( 0 ... d )
                          ( ( P ` k ) x. ( a ^ k ) )
                      )
                      ^ 2
                    )
                    +
                    (
                      (
                        sum_ k e. ( 0 ... e )
                          ( ( Q ` k ) x. ( a ^ k ) )
                      )
                      ^ 2
                    )
                    =
                    ( -u 1 )
                  )
        )
  $.
$}
