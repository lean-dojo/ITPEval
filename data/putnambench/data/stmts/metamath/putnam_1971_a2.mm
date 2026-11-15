$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_a2: classification of real polynomials satisfying
  P(0) = 0 and P(x^2 + 1) = P(x)^2 + 1 for every real x.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is the complete real coefficient function of a polynomial, and d is
  any nonnegative-integer bound beyond which its coefficients vanish.
  Evaluation is the finite coefficient sum through d, hence is independent
  of the chosen valid bound. The right side is exactly the coefficient
  function of X.

  Thus the finite-support coefficient representation ranges over all real
  polynomials and the biconditional is the source classification. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d A d k x $.

  putnambench-putnam-1971-a2 $a |-
    A. A e. ( RR ^m NN0 )
      A. d e. NN0
        (
          A. k e. NN0
            ( d < k -> ( A ` k ) = 0 )
          ->
          (
            (
              ( A ` 0 ) = 0
              /\
              A. x e. RR
                (
                  sum_ k e. ( 0 ... d )
                    (
                      ( A ` k )
                      x.
                      ( ( ( x ^ 2 ) + 1 ) ^ k )
                    )
                  =
                  (
                    (
                      sum_ k e. ( 0 ... d )
                        ( ( A ` k ) x. ( x ^ k ) )
                    )
                    ^ 2
                  )
                  +
                  1
                )
            )
            <->
            (
              (
                ( A ` 0 ) = 0
                /\
                ( A ` 1 ) = 1
              )
              /\
              A. k e. NN0
                ( 1 < k -> ( A ` k ) = 0 )
            )
          )
        )
  $.
$}
