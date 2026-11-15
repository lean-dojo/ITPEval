$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_a6: the least constant bounding the unit-interval integral of
  the absolute value of every real cubic having a root in that interval by
  its maximum absolute value is 5 / 6. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The four real coefficients a, b, c, d with a nonzero represent exactly
  all real polynomials of degree three. P16A6Admissible k says that k has
  the required inequality for every such polynomial having a root in
  [0,1].

  Set.mm's S. binder is the real Lebesgue integral. The ordered supremum is
  taken over all attained absolute values on [0,1]; for a real polynomial
  this nonempty compact image has a maximum, so the supremum is exactly the
  source maximum. The final conjunction expands IsLeast: 5 / 6 is
  admissible, and it is no greater than every other admissible real
  constant. The definition and final declaration are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c P16A6Admissible $.

p16a6-admissible-syntax $a wff ( P16A6Admissible k ) $.

${
  $d a b c d k x y $.

  p16a6-admissible-definition $a |- (
    ( P16A6Admissible k )
    <->
    A. a e. RR
      A. b e. RR
        A. c e. RR
          A. d e. RR
            (
              a =/= 0
              ->
              (
                E. x e. ( 0 [,] 1 )
                  (
                    (
                      (
                        ( a x. ( x ^ 3 ) )
                        +
                        ( b x. ( x ^ 2 ) )
                      )
                      +
                      ( c x. x )
                    )
                    +
                    d
                  )
                  =
                  0
                ->
                S. ( 0 [,] 1 )
                  (
                    abs
                    `
                    (
                      (
                        (
                          ( a x. ( x ^ 3 ) )
                          +
                          ( b x. ( x ^ 2 ) )
                        )
                        +
                        ( c x. x )
                      )
                      +
                      d
                    )
                  )
                  _d x
                <_
                (
                  k
                  x.
                  sup
                    (
                      {
                        y e. RR |
                        E. x e. ( 0 [,] 1 )
                          y
                          =
                          (
                            abs
                            `
                            (
                              (
                                (
                                  ( a x. ( x ^ 3 ) )
                                  +
                                  ( b x. ( x ^ 2 ) )
                                )
                                +
                                ( c x. x )
                              )
                              +
                              d
                            )
                          )
                      } ,
                      RR ,
                      <
                    )
                )
              )
            )
  ) $.
$}

putnambench-putnam-2016-a6 $a |- (
  ( P16A6Admissible ( 5 / 6 ) )
  /\
  A. k e. RR
    (
      ( P16A6Admissible k )
      ->
      ( 5 / 6 ) <_ k
    )
) $.
