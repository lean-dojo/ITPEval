$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_a5: three distinct lattice points on a circle in the real
  Euclidean plane have two points separated by at least the cube root of
  the radius. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P00A5R2 is the real coordinate plane and P00A5Dist is its Euclidean
  distance. The hypothesis S C_ ( ZZ ^m P00A5I ) says that every point has
  two integer coordinates, while ( # ` S ) = 3 makes S a three-element set.
  Thus this set representation is equivalent to the injective Fin 3 indexed
  family in the Lean source and directly matches the Isabelle source.

  Under 0 < r, set.mm's complex-power expression r ^c ( 1 / 3 ) is the
  positive real cube root used by both sources. All point witnesses remain
  internally existentially quantified. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

$c P00A5I P00A5R2 P00A5Dist $.

p00a5-index-syntax $a class P00A5I $.
p00a5-plane-syntax $a class P00A5R2 $.
p00a5-distance-syntax $a class ( P00A5Dist A B ) $.

p00a5-index-definition $a |- P00A5I = ( 1 ... 2 ) $.

p00a5-plane-definition $a |- P00A5R2 = ( RR ^m P00A5I ) $.

${
  $d A B j $.

  p00a5-distance-definition $a |- (
    P00A5Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P00A5I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d P Q S r z $.

  putnambench-putnam-2000-a5 $a |-
    A. r e. RR A. z e. P00A5R2 A. S
      (
        (
          (
            0 < r
            /\
            (
              S C_ ( ZZ ^m P00A5I )
              /\
              ( # ` S ) = 3
            )
          )
          /\
          A. P e. S ( P00A5Dist P z ) = r
        )
        ->
        E. P e. S E. Q e. S
          (
            r ^c ( 1 / 3 )
          )
          <_
          ( P00A5Dist P Q )
      )
  $.
$}
