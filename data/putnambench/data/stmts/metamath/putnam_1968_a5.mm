$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_a5: the sharp bound eight for the absolute derivative at zero
  of a real quadratic bounded in absolute value by one on the closed unit
  interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Every real quadratic is uniquely a*x^2 + b*x + c with a nonzero, and its
  derivative at zero is b. Thus the coefficient formulation below is
  equivalent to quantifying over all degree-two real polynomials. The first
  conjunct states that the bound eight is attained; the second states that
  it is an upper bound for every admissible quadratic. Together these are
  equivalent to the source supremum being eight.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c x $.

  putnambench-putnam-1968-a5 $a |- (
    E. a e. RR E. b e. RR E. c e. RR
      (
        (
          a =/= 0
          /\
          A. x e. RR
            (
              ( 0 <_ x /\ x <_ 1 )
              ->
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
              1
            )
        )
        /\
        ( abs ` b ) = 8
      )
    /\
    A. a e. RR A. b e. RR A. c e. RR
      (
        (
          a =/= 0
          /\
          A. x e. RR
            (
              ( 0 <_ x /\ x <_ 1 )
              ->
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
              1
            )
        )
        ->
        ( abs ` b ) <_ 8
      )
  ) $.
$}
