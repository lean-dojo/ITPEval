$(
  Statement-only formalization of PutnamBench artifact putnam_1963_b1:
  the integer parameter for which the monic quadratic x^2 - x + a divides
  x^13 + x + 90 is exactly two. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly1 ` RRfld is set.mm's ring of finite-support univariate real
  polynomials. The integer a is embedded as a real constant polynomial by
  algSc. The source's integer-polynomial and real-polynomial divisibility
  formulations are equivalent here because the divisor is monic with integer
  coefficients: a quotient over the reals is the unique monic-division
  quotient and has integer coefficients.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  putnambench-putnam-1963-b1 $a |- A. a e. ZZ
    (
      (
        (
          (
            2
            ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
            ( var1 ` RRfld )
          )
          ( -g ` ( Poly1 ` RRfld ) )
          ( var1 ` RRfld )
        )
        ( +g ` ( Poly1 ` RRfld ) )
        ( ( algSc ` ( Poly1 ` RRfld ) ) ` a )
      )
      ( ||r ` ( Poly1 ` RRfld ) )
      (
        (
          (
            ( ( 3 x. 4 ) + 1 )
            ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
            ( var1 ` RRfld )
          )
          ( +g ` ( Poly1 ` RRfld ) )
          ( var1 ` RRfld )
        )
        ( +g ` ( Poly1 ` RRfld ) )
        ( ( algSc ` ( Poly1 ` RRfld ) ) ` ( 9 x. ( 9 + 1 ) ) )
      )
      <->
      a = 2
    )
  $.
$}
