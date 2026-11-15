$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_b2: evaluation of the Gaussian-weighted full-plane integral
  of the number of integer lattice points in the centered disk determined
  by each point, in terms of a Gaussian series. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The restricted class is exactly the set of integer pairs (m,n) satisfying
  m^2 + n^2 <= x^2 + y^2, and # is its finite cardinality. The nested S.
  binders are set.mm's real Lebesgue integrals over the full real line.
  The sum over NN0 is the source series g = sum_k exp(-k^2).

  The right side is the explicit polynomial pi * (2g - 1)^2 recorded in the
  ground-truth solution annotations. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d k p x y $.

  putnambench-putnam-1982-b2 $a |-
    S. RR
      (
        S. RR
          (
            (
              #
              `
              { p e. ( ZZ X. ZZ ) |
                (
                  (
                    ( 1st ` p ) ^ 2
                  )
                  +
                  (
                    ( 2nd ` p ) ^ 2
                  )
                )
                <_
                (
                  ( x ^ 2 )
                  +
                  ( y ^ 2 )
                )
              }
            )
            x.
            (
              exp
              `
              (
                -u
                (
                  ( x ^ 2 )
                  +
                  ( y ^ 2 )
                )
              )
            )
          )
          _d y
      )
      _d x
    =
    (
      _pi
      x.
      (
        (
          2
          x.
          (
            sum_ k e. NN0
              (
                exp
                `
                (
                  -u
                  (
                    k ^ 2
                  )
                )
              )
          )
        )
        -
        1
      )
      ^ 2
    )
  $.
$}
