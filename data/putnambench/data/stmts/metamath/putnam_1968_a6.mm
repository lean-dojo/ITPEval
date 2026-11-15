$(
  Statement-only formalization of PutnamBench artifact putnam_1968_a6:
  classification of nonconstant complex polynomials with coefficients
  plus or minus one and only real roots as twelve explicit polynomials.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A polynomial is represented by its complete coefficient function A from
  NN0 to CC. On the left, the internally quantified positive integer d is
  its degree: the leading coefficient is nonzero, all later coefficients
  vanish, every coefficient through d is plus or minus one, and every
  complex zero of the resulting finite sum is real.

  The right side gives exactly the coefficient functions of
  X - 1, -(X - 1), X + 1, -(X + 1),
  X^2 + X - 1, -(X^2 + X - 1),
  X^2 - X - 1, -(X^2 - X - 1),
  X^3 + X^2 - X - 1, -(X^3 + X^2 - X - 1),
  X^3 - X^2 - X + 1, and -(X^3 - X^2 - X + 1).
  Thus the coefficient-function representation is bidirectionally
  equivalent to the source equality of sets of complex polynomials. The
  declaration below is an unproved $a corpus statement; there is no $p
  proof statement in this database.
$)

${
  $d A d k z $.

  putnambench-putnam-1968-a6 $a |- A. A e. ( CC ^m NN0 )
    (
      (
        E. d e. NN
          (
            ( A ` d ) =/= 0
            /\
            (
              A. k e. NN0
                ( d < k -> ( A ` k ) = 0 )
              /\
              (
                A. k e. ( 0 ... d )
                  (
                    ( A ` k ) = 1
                    \/
                    ( A ` k ) = ( -u 1 )
                  )
                /\
                A. z e. CC
                  (
                    (
                      sum_ k e. ( 0 ... d )
                        ( ( A ` k ) x. ( z ^ k ) )
                    )
                    =
                    0
                    ->
                    z e. RR
                  )
              )
            )
          )
      )
      <->
      (
        (
          A. k e. NN0
            ( 1 < k -> ( A ` k ) = 0 )
          /\
          (
            (
              ( A ` 0 ) = ( -u 1 )
              /\
              ( A ` 1 ) = 1
            )
            \/
            (
              (
                ( A ` 0 ) = 1
                /\
                ( A ` 1 ) = ( -u 1 )
              )
              \/
              (
                (
                  ( A ` 0 ) = 1
                  /\
                  ( A ` 1 ) = 1
                )
                \/
                (
                  ( A ` 0 ) = ( -u 1 )
                  /\
                  ( A ` 1 ) = ( -u 1 )
                )
              )
            )
          )
        )
        \/
        (
          (
            A. k e. NN0
              ( 2 < k -> ( A ` k ) = 0 )
            /\
            (
              (
                (
                  ( A ` 0 ) = ( -u 1 )
                  /\
                  ( A ` 1 ) = 1
                )
                /\
                ( A ` 2 ) = 1
              )
              \/
              (
                (
                  (
                    ( A ` 0 ) = 1
                    /\
                    ( A ` 1 ) = ( -u 1 )
                  )
                  /\
                  ( A ` 2 ) = ( -u 1 )
                )
                \/
                (
                  (
                    (
                      ( A ` 0 ) = ( -u 1 )
                      /\
                      ( A ` 1 ) = ( -u 1 )
                    )
                    /\
                    ( A ` 2 ) = 1
                  )
                  \/
                  (
                    (
                      ( A ` 0 ) = 1
                      /\
                      ( A ` 1 ) = 1
                    )
                    /\
                    ( A ` 2 ) = ( -u 1 )
                  )
                )
              )
            )
          )
          \/
          (
            A. k e. NN0
              ( 3 < k -> ( A ` k ) = 0 )
            /\
            (
              (
                (
                  (
                    ( A ` 0 ) = ( -u 1 )
                    /\
                    ( A ` 1 ) = ( -u 1 )
                  )
                  /\
                  ( A ` 2 ) = 1
                )
                /\
                ( A ` 3 ) = 1
              )
              \/
              (
                (
                  (
                    (
                      ( A ` 0 ) = 1
                      /\
                      ( A ` 1 ) = 1
                    )
                    /\
                    ( A ` 2 ) = ( -u 1 )
                  )
                  /\
                  ( A ` 3 ) = ( -u 1 )
                )
                \/
                (
                  (
                    (
                      (
                        ( A ` 0 ) = 1
                        /\
                        ( A ` 1 ) = ( -u 1 )
                      )
                      /\
                      ( A ` 2 ) = ( -u 1 )
                    )
                    /\
                    ( A ` 3 ) = 1
                  )
                  \/
                  (
                    (
                      (
                        ( A ` 0 ) = ( -u 1 )
                        /\
                        ( A ` 1 ) = 1
                      )
                      /\
                      ( A ` 2 ) = 1
                    )
                    /\
                    ( A ` 3 ) = ( -u 1 )
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
