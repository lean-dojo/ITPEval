$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_b1: for a nonconstant integer polynomial with nonnegative
  coefficients and a positive integer n, divisibility of f(f(n) + 1) by
  f(n) holds exactly when n = 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is set.mm's ring of all finite-support
  univariate polynomials over the integers. The function coe1 extracts the
  complete NN0-indexed coefficient function, and eval1 evaluates a polynomial
  at an integer.

  Universal coefficient nonnegativity and the internally existential positive
  coefficient at an index in NN express exactly the source assumptions that
  every coefficient is nonnegative and that the polynomial is nonconstant.
  The integer n remains arbitrary subject to positivity. Integer divisibility
  and both polynomial evaluations are preserved directly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d f k n $.

  putnambench-putnam-2007-b1 $a |-
    A. f e. ( Base ` ( Poly1 ` ZZring ) )
      A. n e. ZZ
        (
          (
            (
              A. k e. NN0
                0 <_ ( ( coe1 ` f ) ` k )
              /\
              E. k e. NN
                0 < ( ( coe1 ` f ) ` k )
            )
            /\
            0 < n
          )
          ->
          (
            ( ( ( eval1 ` ZZring ) ` f ) ` n )
            ||
            (
              ( ( eval1 ` ZZring ) ` f )
              `
              (
                ( ( ( eval1 ` ZZring ) ` f ) ` n )
                +
                1
              )
            )
            <->
            n = 1
          )
        )
  $.
$}
