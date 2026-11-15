$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_a4: pointwise absolute-value domination between two real
  quadratic polynomials implies domination of the absolute values of their
  discriminants, assuming both leading coefficients are nonzero. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's RR is the full class of real numbers, abs agrees with real absolute
  value on RR, and <_ is the non-strict real order here. All six coefficients
  remain universally quantified, as does the point x in the domination
  hypothesis.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B C a b c x $.

  putnambench-putnam-2003-a4 $a |-
    A. a e. RR A. b e. RR A. c e. RR
    A. A e. RR A. B e. RR A. C e. RR
      (
        (
          (
            a =/= 0
            /\
            A =/= 0
          )
          /\
          A. x e. RR
            (
              abs
              `
              (
                (
                  ( a x. ( x ^ 2 ) )
                  +
                  ( b x. x )
                )
                +
                c
              )
            )
            <_
            (
              abs
              `
              (
                (
                  ( A x. ( x ^ 2 ) )
                  +
                  ( B x. x )
                )
                +
                C
              )
            )
        )
        ->
        (
          abs
          `
          (
            ( b ^ 2 )
            -
            ( ( 4 x. a ) x. c )
          )
        )
        <_
        (
          abs
          `
          (
            ( B ^ 2 )
            -
            ( ( 4 x. A ) x. C )
          )
        )
      )
  $.
$}
