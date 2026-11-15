$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_a1: existence of three real polynomials whose absolute-value
  combination equals the specified three-piece linear function on the real
  line. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` RRfld ) is set.mm's ring of finite-support univariate
  real polynomials, and eval1 evaluates such a polynomial at a real input.
  The source solution annotation is True, so its biconditional with the
  existential proposition is represented by that proposition itself.

  The outer conditional separates x < -1 from x >= -1, and the inner
  conditional separates x <= 0 from x > 0. Thus the three branches and both
  endpoint conventions agree exactly with the Lean and Isabelle sources.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f g h x $.

  putnambench-putnam-1999-a1 $a |-
    E. f e. ( Base ` ( Poly1 ` RRfld ) )
      E. g e. ( Base ` ( Poly1 ` RRfld ) )
        E. h e. ( Base ` ( Poly1 ` RRfld ) )
          A. x e. RR
            (
              (
                (
                  abs
                  `
                  ( ( ( eval1 ` RRfld ) ` f ) ` x )
                )
                -
                (
                  abs
                  `
                  ( ( ( eval1 ` RRfld ) ` g ) ` x )
                )
              )
              +
              ( ( ( eval1 ` RRfld ) ` h ) ` x )
            )
            =
            if
            (
              x < ( -u 1 ) ,
              ( -u 1 ) ,
              if
              (
                x <_ 0 ,
                ( ( 3 x. x ) + 2 ) ,
                ( ( ( -u 2 ) x. x ) + 2 )
              )
            )
  $.
$}
