$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_a2: evaluation of a unit-interval integral involving the
  1992nd Taylor coefficient of (1+x)^alpha and a finite reciprocal sum.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P92A2Coeff alpha is the generalized binomial coefficient

    alpha (alpha-1) ... (alpha-1991) / 1992!,

  which is the coefficient of x^1992 in the Taylor series at zero of
  (1+x)^alpha. The final assertion uses set.mm's real Lebesgue integral
  and retains the source sum over k = 1,...,1992. Its value is the explicit
  solution 1992 supplied by the Rocq ground truth.

  All declarations below are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c P92A2Coeff $.

p92a2-coeff-syntax $a class ( P92A2Coeff a ) $.

${
  $d a k $.

  p92a2-coeff-definition $a |- (
    P92A2Coeff a
  ) = (
    (
      prod_ k e. ( 0 ..^ ; ; ; 1 9 9 2 )
        ( a - k )
    )
    /
    ( ! ` ; ; ; 1 9 9 2 )
  ) $.
$}

${
  $d k y $.

  putnambench-putnam-1992-a2 $a |- (
    S. ( 0 (,) 1 )
      (
        ( P92A2Coeff ( ( -u y ) - 1 ) )
        x.
        sum_ k e. ( 1 ... ; ; ; 1 9 9 2 )
          ( 1 / ( y + k ) )
      )
      _d y
  ) = ; ; ; 1 9 9 2 $.
$}
