$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_a1: equality of the intersections of four real plane curves
  defined by rational and cubic equations. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Expanding the source definitions and applying set extensionality turns
  A intersection B = C intersection D into the pointwise biconditional below
  for every real coordinate pair (x,y). Both source nonzero-denominator
  conditions are retained explicitly.

  The final declaration is the single unproved $a corpus statement; this
  root file contains no $p proof declaration.
$)

${
  $d x y $.

  putnambench-putnam-1987-a1 $a |- A. x e. RR A. y e. RR
    (
      (
        (
          (
            ( ( x ^ 2 ) + ( y ^ 2 ) ) =/= 0
            /\
            (
              ( ( x ^ 2 ) - ( y ^ 2 ) )
              =
              ( x / ( ( x ^ 2 ) + ( y ^ 2 ) ) )
            )
          )
          /\
          (
            ( ( x ^ 2 ) + ( y ^ 2 ) ) =/= 0
            /\
            (
              (
                ( ( 2 x. x ) x. y )
                +
                ( y / ( ( x ^ 2 ) + ( y ^ 2 ) ) )
              )
              =
              3
            )
          )
        )
        <->
        (
          (
            (
              ( x ^ 3 )
              -
              ( ( 3 x. x ) x. ( y ^ 2 ) )
            )
            +
            ( 3 x. y )
          )
          =
          1
          /\
          (
            (
              (
                ( ( 3 x. ( x ^ 2 ) ) x. y )
                -
                ( 3 x. x )
              )
              -
              ( y ^ 3 )
            )
            =
            0
          )
        )
      )
    )
  $.
$}
