$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_a2: a real quadratic form with negative discriminant, even
  after adding arbitrary real cubic terms, has no nonzero zeros in some
  sufficiently small disk about the origin. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A through G range over all real coefficients. The conclusion retains the
  internally existential positive radius and excludes exactly the source's
  real points satisfying the punctured-disk bounds and polynomial equation.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B C D E F G d x y $.

  putnambench-putnam-1970-a2 $a |-
    A. A e. RR
      A. B e. RR
        A. C e. RR
          A. D e. RR
            A. E e. RR
              A. F e. RR
                A. G e. RR
                  (
                    (
                      ( B ^ 2 )
                      -
                      ( ( 4 x. A ) x. C )
                    )
                    <
                    0
                    ->
                    E. d e. RR
                      (
                        0 < d
                        /\
                        -. E. x e. RR E. y e. RR
                          (
                            (
                              (
                                ( x ^ 2 )
                                +
                                ( y ^ 2 )
                              )
                              =/=
                              0
                              /\
                              (
                                (
                                  ( x ^ 2 )
                                  +
                                  ( y ^ 2 )
                                )
                                <
                                ( d ^ 2 )
                              )
                            )
                            /\
                            (
                              (
                                (
                                  (
                                    (
                                      (
                                        (
                                          ( A x. ( x ^ 2 ) )
                                          +
                                          ( ( B x. x ) x. y )
                                        )
                                        +
                                        ( C x. ( y ^ 2 ) )
                                      )
                                      +
                                      ( D x. ( x ^ 3 ) )
                                    )
                                    +
                                    ( ( E x. ( x ^ 2 ) ) x. y )
                                  )
                                  +
                                  ( ( F x. x ) x. ( y ^ 2 ) )
                                )
                                +
                                ( G x. ( y ^ 3 ) )
                              )
                              =
                              0
                            )
                          )
                      )
                  )
  $.
$}
