$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2020_b6: nonnegativity of a finite alternating sum whose exponents
  are floors of multiples of sqrt(2) - 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers, 1 ... n is the inclusive
  interval from 1 through n, sqrt is the principal square root, and |_ is
  the real floor function. Since every summation index is positive and
  sqrt(2) - 1 is positive, each floor exponent is a nonnegative integer, so
  SetMM exponentiation by that value agrees with the source natural/integer
  power of -1.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d k n $.

  putnambench-putnam-2020-b6 $a |- A. n e. NN
    0
    <_
    sum_ k e. ( 1 ... n )
      (
        ( -u 1 )
        ^
        (
          |_ `
          (
            k
            x.
            ( ( sqrt ` 2 ) - 1 )
          )
        )
      )
  $.
$}
