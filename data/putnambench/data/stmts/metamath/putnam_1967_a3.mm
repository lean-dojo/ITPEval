$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_a3: the least positive integer leading coefficient of an
  integer quadratic with two distinct real zeros in the open unit interval
  is 5. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The assertion uses the coefficient form a*x^2 + b*x + c directly. Since
  b ranges over all integers, this is equivalent to the problem's notation
  a*x^2 - b*x + c. Positivity of a makes the polynomial exactly quadratic.
  The first conjunct gives an internal witness with leading coefficient 5;
  the second says every admissible positive integer leading coefficient is
  at least 5. The declaration is an unproved $a statement and contains no
  $p proof.
$)

${
  $d a b c x y $.

  putnambench-putnam-1967-a3 $a |- (
    (
      E. b e. ZZ E. c e. ZZ E. x e. RR E. y e. RR
        (
          ( 0 < x /\ x < 1 )
          /\
          (
            ( 0 < y /\ y < 1 )
            /\
            (
              x =/= y
              /\
              (
                (
                  (
                    ( 5 x. ( x ^ 2 ) )
                    +
                    ( b x. x )
                  )
                  +
                  c
                )
                =
                0
                /\
                (
                  (
                    ( 5 x. ( y ^ 2 ) )
                    +
                    ( b x. y )
                  )
                  +
                  c
                )
                =
                0
              )
            )
          )
        )
    )
    /\
    A. a e. ZZ A. b e. ZZ A. c e. ZZ
      (
        (
          0 < a
          /\
          E. x e. RR E. y e. RR
            (
              ( 0 < x /\ x < 1 )
              /\
              (
                ( 0 < y /\ y < 1 )
                /\
                (
                  x =/= y
                  /\
                  (
                    (
                      (
                        ( a x. ( x ^ 2 ) )
                        +
                        ( b x. x )
                      )
                      +
                      c
                    )
                    =
                    0
                    /\
                    (
                      (
                        ( a x. ( y ^ 2 ) )
                        +
                        ( b x. y )
                      )
                      +
                      c
                    )
                    =
                    0
                  )
                )
              )
            )
        )
        ->
        5 <_ a
      )
  ) $.
$}
