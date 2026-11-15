$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_a2 (putnambench__metamath__putnam_2024_a2): the real
  polynomials p for which p(p(x)) - x is (p(x) - x)^2 times a real
  polynomial are exactly the affine polynomials with slope 1 or -1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` RRfld ) is set.mm's ring of all finite-support
  univariate real polynomials, and eval1 is ordinary polynomial evaluation.
  The left restricted class preserves the internally existential polynomial
  Q and the universal real variable x from the source statement.

  On the right, algSc embeds a real number as a constant polynomial.
  Thus X + a and a - X are exactly the source solution family
  s X + a for integer units s, since the only integer units are 1 and -1.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d P Q a x $.

  putnambench-putnam-2024-a2 $a |-
    {
      P e. ( Base ` ( Poly1 ` RRfld ) )
      |
      E. Q e. ( Base ` ( Poly1 ` RRfld ) )
        A. x e. RR
          (
            (
              (
                ( ( eval1 ` RRfld ) ` P )
                `
                (
                  ( ( eval1 ` RRfld ) ` P )
                  `
                  x
                )
              )
              -
              x
            )
            =
            (
              (
                (
                  ( ( eval1 ` RRfld ) ` P )
                  `
                  x
                )
                -
                x
              )
              ^
              2
            )
            x.
            (
              ( ( eval1 ` RRfld ) ` Q )
              `
              x
            )
          )
    }
    =
    {
      P e. ( Base ` ( Poly1 ` RRfld ) )
      |
      E. a e. RR
        (
          P
          =
          (
            ( var1 ` RRfld )
            ( +g ` ( Poly1 ` RRfld ) )
            ( ( algSc ` ( Poly1 ` RRfld ) ) ` a )
          )
          \/
          P
          =
          (
            ( ( algSc ` ( Poly1 ` RRfld ) ) ` a )
            ( -g ` ( Poly1 ` RRfld ) )
            ( var1 ` RRfld )
          )
        )
    }
  $.
$}
