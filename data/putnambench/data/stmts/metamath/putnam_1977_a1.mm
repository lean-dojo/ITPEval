$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_a1: four distinct points on the real quartic
  2x^4 + 7x^3 + 3x - 5 that lie on one line have average x-coordinate
  -7/8. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The four distinct inputs are represented by a four-element subset S of RR.
  Since their curve points form a graph with distinct x-coordinates,
  collinearity is equivalent to the internally existential real slope m and
  intercept b making the quartic equal m x + b at every x in S.

  The conclusion uses the finite-set sum over S, exactly matching the average
  x-coordinate in the source statements. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d S b m x $.

  putnambench-putnam-1977-a1 $a |-
    (
      (
        (
          S C_ RR
          /\
          ( # ` S ) = 4
        )
        /\
        E. m e. RR E. b e. RR
          A. x e. S
            (
              (
                (
                  (
                    ( 2 x. ( x ^ 4 ) )
                    +
                    ( 7 x. ( x ^ 3 ) )
                  )
                  +
                  ( 3 x. x )
                )
                -
                5
              )
              =
              ( ( m x. x ) + b )
            )
      )
      ->
      (
        ( ( sum_ x e. S x ) / 4 )
        =
        ( -u ( 7 / 8 ) )
      )
    )
  $.
$}
