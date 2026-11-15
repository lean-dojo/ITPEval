$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2012_a6: a continuous real-valued function on the real plane
  vanishes identically if its integral over every axis-aligned rectangle
  of area one is zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions on RR X. RR. Joint
  continuity is expanded in epsilon-delta form using coordinatewise
  neighborhoods, which induce the standard product topology.

  Set.mm's S. binder is the real Lebesgue integral. The nested integrals over
  closed intervals agree with the source interval integrals, and for
  continuous functions also with the two-dimensional rectangle integral in
  the Isabelle source. The restrictions a < b and c < k preserve the
  source's positive side lengths, while their product is required to equal
  one.

  The source packages the affirmative claim as an equivalence with the
  solution proposition True. The final declaration states that affirmative
  claim directly, an equivalent formulation. It is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d F a b c d e k u v x y $.

  putnambench-putnam-2012-a6 $a |-
    A. F e. ( RR ^m ( RR X. RR ) )
      (
        (
          A. x e. RR A. y e. RR A. e e. RR
            (
              0 < e
              ->
              E. d e. RR
                (
                  0 < d
                  /\
                  A. u e. RR A. v e. RR
                    (
                      (
                        ( abs ` ( u - x ) ) < d
                        /\
                        ( abs ` ( v - y ) ) < d
                      )
                      ->
                      (
                        abs
                        `
                        (
                          ( F ` <. u , v >. )
                          -
                          ( F ` <. x , y >. )
                        )
                      )
                      < e
                    )
                )
            )
          /\
          A. a e. RR A. b e. RR A. c e. RR A. k e. RR
            (
              (
                (
                  a < b
                  /\
                  c < k
                )
                /\
                ( ( b - a ) x. ( k - c ) ) = 1
              )
              ->
              (
                S. ( a [,] b )
                  (
                    S. ( c [,] k )
                      ( F ` <. x , y >. )
                      _d y
                  )
                  _d x
              )
              =
              0
            )
        )
        ->
        A. x e. RR A. y e. RR
          ( F ` <. x , y >. ) = 0
      )
  $.
$}
