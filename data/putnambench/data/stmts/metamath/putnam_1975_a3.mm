$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_a3: the explicit maximum and minimum points of
  x^a + y^b + z^c on the nonnegative surface x^b + y^b + z^b = 1
  when 0 < a < b < c. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  All quantified scalars range over the full real numbers. On nonnegative
  real bases and the positive real exponents occurring here, set.mm's
  complex-power operation ^c is the source real-power operation, including
  its value zero at base zero.

  The internally quantified u, v, s, and w are tied by equality to the four
  nonzero coordinates of the two explicit solution points: (u,v,0) is the
  maximum point and (0,s,w) is the minimum point. Inlining these equalities
  gives exactly the solution functions and the predicates P and f in the
  ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c s u v w x y z $.

  putnambench-putnam-1975-a3 $a |-
    A. a e. RR A. b e. RR A. c e. RR
      (
        (
          0 < a
          /\
          (
            a < b
            /\
            b < c
          )
        )
        ->
        E. u e. RR E. v e. RR E. s e. RR E. w e. RR
          (
            u =
              (
                ( a / b )
                ^c
                ( 1 / ( b - a ) )
              )
            /\
            (
              v =
                (
                  (
                    1
                    -
                    ( u ^c b )
                  )
                  ^c
                  ( 1 / b )
                )
              /\
              (
                s =
                  (
                    (
                      1
                      -
                      ( w ^c b )
                    )
                    ^c
                    ( 1 / b )
                  )
                /\
                (
                  w =
                    (
                      ( b / c )
                      ^c
                      ( 1 / ( c - b ) )
                    )
                  /\
                  (
                    (
                      (
                        (
                          0 <_ u
                          /\
                          0 <_ v
                        )
                        /\
                        0 <_ 0
                      )
                      /\
                      (
                        (
                          ( u ^c b )
                          +
                          ( v ^c b )
                        )
                        +
                        ( 0 ^c b )
                      )
                      =
                      1
                    )
                    /\
                    (
                      A. x e. RR A. y e. RR A. z e. RR
                        (
                          (
                            (
                              (
                                (
                                  0 <_ x
                                  /\
                                  0 <_ y
                                )
                                /\
                                0 <_ z
                              )
                              /\
                              (
                                (
                                  ( x ^c b )
                                  +
                                  ( y ^c b )
                                )
                                +
                                ( z ^c b )
                              )
                              =
                              1
                            )
                            ->
                            (
                              (
                                ( x ^c a )
                                +
                                ( y ^c b )
                              )
                              +
                              ( z ^c c )
                            )
                            <_
                            (
                              (
                                ( u ^c a )
                                +
                                ( v ^c b )
                              )
                              +
                              ( 0 ^c c )
                            )
                          )
                        )
                      /\
                      (
                        (
                          (
                            (
                              0 <_ 0
                              /\
                              0 <_ s
                            )
                            /\
                            0 <_ w
                          )
                          /\
                          (
                            (
                              ( 0 ^c b )
                              +
                              ( s ^c b )
                            )
                            +
                            ( w ^c b )
                          )
                          =
                          1
                        )
                        /\
                        A. x e. RR A. y e. RR A. z e. RR
                          (
                            (
                              (
                                (
                                  (
                                    0 <_ x
                                    /\
                                    0 <_ y
                                  )
                                  /\
                                  0 <_ z
                                )
                                /\
                                (
                                  (
                                    ( x ^c b )
                                    +
                                    ( y ^c b )
                                  )
                                  +
                                  ( z ^c b )
                                )
                                =
                                1
                              )
                              ->
                              (
                                (
                                  ( x ^c a )
                                  +
                                  ( y ^c b )
                                )
                                +
                                ( z ^c c )
                              )
                              >_
                              (
                                (
                                  ( 0 ^c a )
                                  +
                                  ( s ^c b )
                                )
                                +
                                ( w ^c c )
                              )
                            )
                          )
                      )
                    )
                  )
                )
              )
            )
          )
      )
  $.
$}
