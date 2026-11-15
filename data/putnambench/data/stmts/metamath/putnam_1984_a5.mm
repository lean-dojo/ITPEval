$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_a5: evaluation of a factorial-weighted monomial integral over
  the nonnegative three-dimensional unit simplex. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  The nested S. binders are set.mm's real Lebesgue integrals. Their closed
  intervals describe exactly the simplex slices

    0 <= z <= 1,  0 <= y <= 1-z,  0 <= x <= 1-y-z.

  The integrand is x^1 y^9 z^8 (1-x-y-z)^4. The right side retains all four
  positive factorial parameters from the Lean and Isabelle answer tuple;
  its 1! factor is one, so it is the same value as the Rocq expression
  9! 8! 4! / 25!. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d x y z $.

  putnambench-putnam-1984-a5 $a |-
    S. ( 0 [,] 1 )
      (
        S. ( 0 [,] ( 1 - z ) )
          (
            S. ( 0 [,] ( ( 1 - y ) - z ) )
              (
                (
                  (
                    (
                      ( x ^ 1 )
                      x.
                      ( y ^ 9 )
                    )
                    x.
                    ( z ^ 8 )
                  )
                  x.
                  ( ( ( ( 1 - x ) - y ) - z ) ^ 4 )
                )
              )
              _d x
          )
          _d y
      )
      _d z
    =
    (
      (
        (
          (
            ( ! ` 1 )
            x.
            ( ! ` 9 )
          )
          x.
          ( ! ` 8 )
        )
        x.
        ( ! ` 4 )
      )
      /
      ( ! ` ; 2 5 )
    )
  $.
$}
