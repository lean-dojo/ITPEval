$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_b4: classification of pairs of real polynomials satisfying
  p(x)q(x+1) - p(x+1)q(x) = 1 for every real x. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly1 ` RRfld is set.mm's ring of all finite-support univariate real
  polynomials, and eval1 is ordinary polynomial evaluation. The right side
  states internally that p(x) = ax + b and q(x) = cx + d for real
  coefficients with b*c - a*d = 1. This is exactly the coefficient
  characterization recorded by the ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d a b c d p q x $.

  putnambench-putnam-2010-b4 $a |-
    A. p e. ( Base ` ( Poly1 ` RRfld ) )
    A. q e. ( Base ` ( Poly1 ` RRfld ) )
      (
        A. x e. RR
          (
            (
              (
                ( ( eval1 ` RRfld ) ` p )
                `
                x
              )
              x.
              (
                ( ( eval1 ` RRfld ) ` q )
                `
                ( x + 1 )
              )
            )
            -
            (
              (
                ( ( eval1 ` RRfld ) ` p )
                `
                ( x + 1 )
              )
              x.
              (
                ( ( eval1 ` RRfld ) ` q )
                `
                x
              )
            )
            =
            1
          )
        <->
        E. a e. RR E. b e. RR E. c e. RR E. d e. RR
          (
            (
              p
              =
              (
                (
                  ( ( algSc ` ( Poly1 ` RRfld ) ) ` a )
                  ( .r ` ( Poly1 ` RRfld ) )
                  ( var1 ` RRfld )
                )
                ( +g ` ( Poly1 ` RRfld ) )
                ( ( algSc ` ( Poly1 ` RRfld ) ) ` b )
              )
              /\
              q
              =
              (
                (
                  ( ( algSc ` ( Poly1 ` RRfld ) ) ` c )
                  ( .r ` ( Poly1 ` RRfld ) )
                  ( var1 ` RRfld )
                )
                ( +g ` ( Poly1 ` RRfld ) )
                ( ( algSc ` ( Poly1 ` RRfld ) ) ` d )
              )
            )
            /\
            (
              ( b x. c )
              -
              ( a x. d )
            )
            =
            1
          )
      )
  $.
$}
