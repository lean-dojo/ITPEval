$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_b5: evaluation of an improper exponential integral on the
  positive real half-line, assuming the Gaussian integral identity. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The premise is the source assumption that the integral of exp(-x^2) over
  the full real line is sqrt(pi). The conclusion uses set.mm's real Lebesgue
  integral over the open positive half-line.

  On this domain t is positive, so t ^c (-(1/2)) agrees with the source real
  power t^(-1/2), and 1 / t agrees with the source inverse power. The right
  side is the explicit value supplied by the Rocq source and recorded in the
  Lean and Isabelle solution annotations. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d t x $.

  putnambench-putnam-1985-b5 $a |- (
    (
      S. RR
        (
          exp
          `
          (
            -u
            ( x ^ 2 )
          )
        )
        _d x
      =
      ( sqrt ` _pi )
    )
    ->
    (
      S. ( 0 (,) +oo )
        (
          (
            t
            ^c
            (
              -u
              ( 1 / 2 )
            )
          )
          x.
          (
            exp
            `
            (
              -u
              (
                ( ; ; ; 1 9 8 5 )
                x.
                (
                  t
                  +
                  ( 1 / t )
                )
              )
            )
          )
        )
        _d t
      =
      (
        (
          sqrt
          `
          (
            _pi
            /
            ( ; ; ; 1 9 8 5 )
          )
        )
        x.
        (
          exp
          `
          (
            -u
            ( ; ; ; 3 9 7 0 )
          )
        )
      )
    )
  ) $.
$}
