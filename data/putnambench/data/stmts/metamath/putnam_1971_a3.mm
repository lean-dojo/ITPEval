$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_a3: the product of the three side lengths of a triangle
  with distinct lattice-point vertices on a circle of positive radius
  is at least twice the radius. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The Euclidean plane is represented isometrically by CC. A point is a
  lattice point exactly when its real and imaginary parts are integers,
  and complex absolute value is Euclidean distance. Thus the existential
  center, positive radius, pairwise distinctness, and distance-product
  inequality are the source hypotheses and conclusion without restriction.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A B C O r $.

  putnambench-putnam-1971-a3 $a |-
    A. A e. CC A. B e. CC A. C e. CC A. r e. RR+
      (
        (
        (
          (
            (
              ( Re ` A ) e. ZZ
              /\
              ( Im ` A ) e. ZZ
            )
            /\
            (
              ( Re ` B ) e. ZZ
              /\
              ( Im ` B ) e. ZZ
            )
          )
          /\
          (
            (
              ( Re ` C ) e. ZZ
              /\
              ( Im ` C ) e. ZZ
            )
            /\
            (
              (
                A =/= B
                /\
                A =/= C
              )
              /\
              B =/= C
            )
          )
        )
        /\
        E. O e. CC
          (
            (
              ( abs ` ( A - O ) ) = r
              /\
              ( abs ` ( B - O ) ) = r
            )
            /\
            ( abs ` ( C - O ) ) = r
          )
        )
        ->
          (
            ( 2 x. r )
            <_
            (
              (
                ( abs ` ( A - B ) )
                x.
                ( abs ` ( A - C ) )
              )
              x.
              ( abs ` ( B - C ) )
            )
          )
      )
  $.
$}
