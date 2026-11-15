$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_b6: every continuous real-valued function satisfies the stated
  absolute-value integral inequality on the unit square. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  Membership in RR -cn-> RR is set.mm's native class of globally continuous
  real-valued functions, matching the continuity assumption in all supplied
  formal sources. The nested S. binders are real Lebesgue integrals over the
  closed unit interval. Endpoint inclusion does not change these integrals,
  so they agree with the source interval integrals and with the product-space
  integral in the Isabelle source.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F x y $.

  putnambench-putnam-2003-b6 $a |-
    A. F e. ( RR -cn-> RR )
      (
        S. ( 0 [,] 1 )
          ( abs ` ( F ` x ) )
          _d x
      )
      <_
      (
        S. ( 0 [,] 1 )
          (
            S. ( 0 [,] 1 )
              (
                abs
                `
                (
                  ( F ` x )
                  +
                  ( F ` y )
                )
              )
              _d y
          )
          _d x
      )
  $.
$}
