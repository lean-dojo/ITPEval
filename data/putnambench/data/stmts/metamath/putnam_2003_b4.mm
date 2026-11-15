$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_b4: rationality of the product of two roots of an
  integer-coefficient quartic when their sum is rational and differs from
  the sum of the other two roots. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The integer coefficients a through e and real roots p, q, r, s correspond
  to a, b, c, d, e and r1, r2, r3, r4 in the ground-truth statements. The
  pointwise equality directly identifies the quartic polynomial with its
  four-real-root factorization. This eliminates the auxiliary function f
  definitionally: either source pair of equations implies this equality, and
  this equality recovers the source equations by taking f to be the displayed
  polynomial.

  Membership in QQ is exactly rationality of the real sum or product. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d a b c d e p q r s x $.

  putnambench-putnam-2003-b4 $a |-
    A. a e. ZZ A. b e. ZZ A. c e. ZZ
      A. d e. ZZ A. e e. ZZ
        A. p e. RR A. q e. RR A. r e. RR A. s e. RR
          (
            (
              a =/= 0
              /\
              A. x e. RR
                (
                  (
                    (
                      (
                        (
                          ( a x. ( x ^ 4 ) )
                          +
                          ( b x. ( x ^ 3 ) )
                        )
                        +
                        ( c x. ( x ^ 2 ) )
                      )
                      +
                      ( d x. x )
                    )
                    +
                    e
                  )
                  =
                  (
                    (
                      (
                        ( a x. ( x - p ) )
                        x.
                        ( x - q )
                      )
                      x.
                      ( x - r )
                    )
                    x.
                    ( x - s )
                  )
                )
            )
            ->
            (
              (
                ( p + q ) e. QQ
                /\
                ( p + q ) =/= ( r + s )
              )
              ->
              ( p x. q ) e. QQ
            )
          )
  $.
$}
