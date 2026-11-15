$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_b3: a restricted two-variable real limit involving an
  iterated power series over positive index pairs. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  P99B3Series(x,y) is the source's iterated sum over
  nonnegative integer indices, with the summand set to zero unless both
  indices are positive and their real ratio lies between 1/2 and 2.

  The final assertion expands convergence within
  A = { (x,y) in RR X. RR | 0 <= x < 1 and 0 <= y < 1 } into an
  epsilon-delta condition. Coordinatewise open delta-neighborhoods form a
  neighborhood basis for the product topology on RR X. RR, so this is
  equivalent to the source Tendsto/filterlim statement.

  Every declaration is an unproved $a statement, and this database contains
  no $p proof statement.
$)

$c P99B3Series $.

p99b3-series-syntax $a class ( P99B3Series x y ) $.

${
  $d m n x y $.

  p99b3-series-definition $a |- (
    ( P99B3Series x y )
    =
    (
      sum_ m e. NN0
        (
          sum_ n e. NN0
            if (
              (
                ( 0 < m /\ 0 < n )
                /\
                (
                  ( 1 / 2 ) <_ ( m / n )
                  /\
                  ( m / n ) <_ 2
                )
              ) ,
              ( ( x ^ m ) x. ( y ^ n ) ) ,
              0
            )
        )
    )
  ) $.
$}

${
  $d d e x y $.

  putnambench-putnam-1999-b3 $a |-
    A. e e. RR
      (
        0 < e
        ->
        E. d e. RR
          (
            0 < d
            /\
            A. x e. RR A. y e. RR
              (
                (
                  (
                    ( 0 <_ x /\ x < 1 )
                    /\
                    ( 0 <_ y /\ y < 1 )
                  )
                  /\
                  (
                    ( abs ` ( x - 1 ) ) < d
                    /\
                    ( abs ` ( y - 1 ) ) < d
                  )
                )
                ->
                (
                  abs
                  `
                  (
                    (
                      (
                        (
                          1
                          -
                          ( x x. ( y ^ 2 ) )
                        )
                        x.
                        (
                          1
                          -
                          ( ( x ^ 2 ) x. y )
                        )
                      )
                      x.
                      ( P99B3Series x y )
                    )
                    -
                    3
                  )
                )
                < e
              )
          )
      )
  $.
$}
