$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_a1: the equivalence between an integer being a sum of two
  triangular numbers and four times that integer plus one being a sum of
  two integer squares, with explicit forward witnesses. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  All variables are restricted to set.mm's class ZZ of integers. Since
  a^2 + a and b^2 + b are even, division by 2 agrees with the exact
  rational or real division in the Lean and Rocq sources and with the
  integer division in Isabelle.

  Substituting x = a + b + 1 and y = a - b makes the square-sum equation
  algebraically equivalent to the triangular-number equation. Thus the
  forward biconditional matches Rocq and is bidirectionally equivalent to
  the forward implication in Lean and Isabelle. The second conjunct keeps
  the square witnesses and triangular-number witnesses internally
  existentially quantified.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b n x y $.

  putnambench-putnam-1975-a1 $a |- (
    (
      A. n e. ZZ A. a e. ZZ A. b e. ZZ
        (
          n =
            (
              ( ( ( a ^ 2 ) + a ) / 2 )
              +
              ( ( ( b ^ 2 ) + b ) / 2 )
            )
          <->
          ( ( 4 x. n ) + 1 ) =
            (
              ( ( ( a + b ) + 1 ) ^ 2 )
              +
              ( ( a - b ) ^ 2 )
            )
        )
    )
    /\
    A. n e. ZZ
      (
        (
          E. x e. ZZ E. y e. ZZ
            ( ( 4 x. n ) + 1 ) =
              ( ( x ^ 2 ) + ( y ^ 2 ) )
        )
        ->
        E. a e. ZZ E. b e. ZZ
          n =
            (
              ( ( ( a ^ 2 ) + a ) / 2 )
              +
              ( ( ( b ^ 2 ) + b ) / 2 )
            )
      )
  ) $.
$}
