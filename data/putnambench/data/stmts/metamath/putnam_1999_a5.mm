$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_a5: a universal real constant bounds the absolute value at zero
  of every real polynomial of exact degree 1999 by its absolute-value integral
  over the interval from -1 to 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly ` RR is set.mm's class of polynomial functions with real
  coefficients, deg gives their exact degree, and function application is
  polynomial evaluation. Thus P ranges over the full source domain of real
  polynomials of exact degree 1999 rather than a finite coefficient table.

  The S. binder is the real Lebesgue integral. Its closed interval differs
  from the source interval-integral presentation only at the two endpoints,
  which does not change the integral. The existential C precedes the
  universal polynomial quantifier, so one constant works for every such
  polynomial.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d C P x $.

  putnambench-putnam-1999-a5 $a |-
    E. C e. RR
      A. P e. ( Poly ` RR )
        (
          ( deg ` P ) = ; ; ; 1 9 9 9
          ->
          (
            abs
            `
            ( P ` 0 )
          )
          <_
          (
            C
            x.
            S. ( ( -u 1 ) [,] 1 )
              (
                abs
                `
                ( P ` x )
              )
              _d x
          )
        )
  $.
$}
