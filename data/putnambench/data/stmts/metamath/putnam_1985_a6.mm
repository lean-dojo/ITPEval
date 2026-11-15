$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_a6: the real polynomials 3x^2 + 7x + 2 and
  6x^2 + 5x + 1 have equal sums of squared coefficients in every
  positive integral power, and the latter polynomial has value 1 at zero.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly1 ` RRfld is set.mm's ring of finite-support univariate real
  polynomials, var1 is its indeterminate, and algSc embeds real constants.
  P85A6F and P85A6G are respectively the source polynomial f and the explicit
  solution g recorded by every ground-truth source.

  The coefficient map coe1 sends a polynomial to its complete NN0-indexed
  coefficient function. Because this function has finite support, summing its
  squared values over NN0 is definitionally the source quantity Gamma. The
  exponentiation in the final assertion is polynomial-ring exponentiation,
  and NN is exactly the source range of natural n with n >= 1.

  All declarations below are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c P85A6F P85A6G P85A6Gamma $.

p85a6-f-syntax $a class P85A6F $.
p85a6-g-syntax $a class P85A6G $.
p85a6-gamma-syntax $a class P85A6Gamma $.

p85a6-f-definition $a |- P85A6F =
  (
    (
      (
        ( ( algSc ` ( Poly1 ` RRfld ) ) ` 3 )
        ( .r ` ( Poly1 ` RRfld ) )
        (
          2
          ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
          ( var1 ` RRfld )
        )
      )
      ( +g ` ( Poly1 ` RRfld ) )
      (
        ( ( algSc ` ( Poly1 ` RRfld ) ) ` 7 )
        ( .r ` ( Poly1 ` RRfld ) )
        ( var1 ` RRfld )
      )
    )
    ( +g ` ( Poly1 ` RRfld ) )
    ( ( algSc ` ( Poly1 ` RRfld ) ) ` 2 )
  ) $.

p85a6-g-definition $a |- P85A6G =
  (
    (
      (
        ( ( algSc ` ( Poly1 ` RRfld ) ) ` 6 )
        ( .r ` ( Poly1 ` RRfld ) )
        (
          2
          ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
          ( var1 ` RRfld )
        )
      )
      ( +g ` ( Poly1 ` RRfld ) )
      (
        ( ( algSc ` ( Poly1 ` RRfld ) ) ` 5 )
        ( .r ` ( Poly1 ` RRfld ) )
        ( var1 ` RRfld )
      )
    )
    ( +g ` ( Poly1 ` RRfld ) )
    ( ( algSc ` ( Poly1 ` RRfld ) ) ` 1 )
  ) $.

${
  $d k p $.

  p85a6-gamma-definition $a |- P85A6Gamma =
    (
      p e. ( Base ` ( Poly1 ` RRfld ) ) |->
        sum_ k e. NN0
          ( ( ( ( coe1 ` p ) ` k ) ) ^ 2 )
    ) $.
$}

putnambench-putnam-1985-a6 $a |- (
  (
    ( ( ( eval1 ` RRfld ) ` P85A6G ) ` 0 )
    =
    1
  )
  /\
  A. n e. NN
    (
      P85A6Gamma
      `
      (
        n
        ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
        P85A6F
      )
    )
    =
    (
      P85A6Gamma
      `
      (
        n
        ( .g ` ( mulGrp ` ( Poly1 ` RRfld ) ) )
        P85A6G
      )
    )
  ) $.
