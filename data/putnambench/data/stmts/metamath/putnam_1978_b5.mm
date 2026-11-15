$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_b5: the degree-four real polynomial 4x^4 - 4x^2 + 1 maps
  [-1, 1] into [0, 1] and has the largest possible leading coefficient
  among all degree-four real polynomials with that range property.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A polynomial is represented by its complete real coefficient function f
  on NN0. The conditions f(4) != 0 and f(k) = 0 for k > 4 say exactly that
  its degree is four, and the finite sum from 0 through 4 is its evaluation.

  The explicit solution from the Rocq source and the Lean and Isabelle
  annotations is inlined as 4x^4 - 4x^2 + 1. Its leading coefficient is 4.
  Thus the first conjunct states that this solution has degree four and maps
  [-1, 1] into [0, 1], while the second states that every polynomial with
  those properties has fourth coefficient at most 4.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f k x $.

  putnambench-putnam-1978-b5 $a |- (
    (
      4 =/= 0
      /\
      A. x e. ( ( -u 1 ) [,] 1 )
        (
          (
            ( 4 x. ( x ^ 4 ) )
            -
            ( 4 x. ( x ^ 2 ) )
          )
          +
          1
        )
        e. ( 0 [,] 1 )
    )
    /\
    A. f e. ( RR ^m NN0 )
      (
        (
          (
            ( f ` 4 ) =/= 0
            /\
            A. k e. NN0
              (
                4 < k
                ->
                ( f ` k ) = 0
              )
          )
          /\
          A. x e. ( ( -u 1 ) [,] 1 )
            (
              sum_ k e. ( 0 ... 4 )
                (
                  ( f ` k )
                  x.
                  ( x ^ k )
                )
            )
            e. ( 0 [,] 1 )
        )
        ->
        ( f ` 4 ) <_ 4
      )
  ) $.
$}
