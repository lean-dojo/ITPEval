$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_a5: a nonconstant real polynomial has only finitely many real
  endpoints where both its sine-weighted and cosine-weighted oriented
  integrals from zero vanish. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly1 ` RRfld is set.mm's ring of finite-support univariate polynomials
  over the reals. The map algSc embeds real constants, so excluding its
  image says exactly that P is nonconstant. The map eval1 evaluates P.

  P80A5Integral P F x is the oriented integral from zero to x of
  P(t)F(t). For nonnegative x it is the Lebesgue integral over (0,x);
  for negative x it is the negative of the integral over (x,0). Endpoint
  inclusion is immaterial, so this is definitionally equivalent to the
  interval integrals in the Lean and Isabelle sources for every real x.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P80A5Integral $.

p80a5-integral-syntax $a class ( P80A5Integral P F x ) $.

${
  $d F P t x $.

  p80a5-integral-definition $a |- (
    ( P80A5Integral P F x )
    =
    if (
      0 <_ x ,
      S. ( 0 (,) x )
        (
          (
            (
              ( ( eval1 ` RRfld ) ` P )
              `
              t
            )
            x.
            ( F ` t )
          )
        )
        _d t ,
      -u
      S. ( x (,) 0 )
        (
          (
            (
              ( ( eval1 ` RRfld ) ` P )
              `
              t
            )
            x.
            ( F ` t )
          )
        )
        _d t
    )
  ) $.
$}

${
  $d c p x $.

  putnambench-putnam-1980-a5 $a |-
    A. p e. ( Base ` ( Poly1 ` RRfld ) )
      (
        -.
        E. c e. RR
          p = ( ( algSc ` ( Poly1 ` RRfld ) ) ` c )
        ->
        {
          x e. RR |
          (
            ( P80A5Integral p sin x ) = 0
            /\
            ( P80A5Integral p cos x ) = 0
          )
        }
        e. Fin
      )
  $.
$}
