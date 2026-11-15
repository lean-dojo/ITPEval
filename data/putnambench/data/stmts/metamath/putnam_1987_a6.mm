$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_a6: the positive real parameters for which the series whose
  nth term is x raised to the number of zeroes in the base-three expansion
  of n, divided by n cubed, converges. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, P87A6A(n) counts the nonnegative positions k at or below
  the leading base-three digit for which floor(n / 3^k) modulo 3 is zero.
  Thus it is exactly the number of zeroes in the base-three representation
  used by both ground-truth sources. Restricting the series index to NN
  removes only their n = 0 term, which is zero because real division by zero
  is totalized to zero.

  In set.mm an unbounded sum belongs to RR exactly when its real partial sums
  converge. Therefore the left side is the source set of positive real x for
  which the series is summable, and the right side is its annotated solution
  set 0 < x < 25. All declarations are unproved $a statement encodings; this
  database contains no $p proof declaration.
$)

$c P87A6A $.

p87a6-a-syntax $a class P87A6A $.

${
  $d k n $.

  p87a6-a-definition $a |- P87A6A =
    (
      n e. NN |->
        (
          # `
          {
            k e. NN0 |
            (
              ( 3 ^ k ) <_ n
              /\
              (
                (
                  ( |_ ` ( n / ( 3 ^ k ) ) )
                  mod
                  3
                )
                =
                0
              )
            )
          }
        )
    )
  $.
$}

${
  $d n x $.

  putnambench-putnam-1987-a6 $a |-
    {
      x e. RR |
      (
        0 < x
        /\
        (
          sum_ n e. NN
            (
              ( x ^ ( P87A6A ` n ) )
              /
              ( n ^ 3 )
            )
        )
        e. RR
      )
    }
    =
    {
      x e. RR |
      (
        0 < x
        /\
        x < ; 2 5
      )
    }
  $.
$}
