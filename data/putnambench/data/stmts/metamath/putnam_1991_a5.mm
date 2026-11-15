$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_a5: the maximum over real y in [0,1] of the integral from
  zero to y of sqrt(x^4 + (y - y^2)^2) is 1/3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P91A5Integral y is set.mm's real Lebesgue integral over the open interval
  (0,y). Since the final statement restricts y to [0,1], this agrees with
  the source oriented interval integral; omitting the two endpoints does not
  change the integral.

  The conjunction in the final assertion states both that the value 1/3 is
  attained and that it is an upper bound for every y in [0,1], which is
  exactly the source greatest-value formulation. All declarations below are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
$)

$c P91A5Integral $.

p91a5-integral-syntax $a class ( P91A5Integral y ) $.

${
  $d x y $.

  p91a5-integral-definition $a |- (
    P91A5Integral y
  ) = (
    S. ( 0 (,) y )
      (
        sqrt
        `
        (
          ( x ^ 4 )
          +
          ( ( y - ( y ^ 2 ) ) ^ 2 )
        )
      )
      _d x
  ) $.
$}

putnambench-putnam-1991-a5 $a |- (
  E. y e. ( 0 [,] 1 )
    ( P91A5Integral y ) = ( 1 / 3 )
  /\
  A. y e. ( 0 [,] 1 )
    ( P91A5Integral y ) <_ ( 1 / 3 )
) $.
