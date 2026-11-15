$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_a3: every four-coloring of the closed isosceles right
  triangle with vertices (0,0), (1,0), and (0,1) has two same-colored
  points at distance at least 2 - sqrt(2). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P94A3R2 is the full real coordinate plane. P94A3Triangle is the closed
  triangle x_1 >= 0, x_2 >= 0, x_1 + x_2 <= 1. This is exactly the convex
  hull in the sources: the barycentric weights of (0,0), (1,0), and (0,1)
  are 1 - x_1 - x_2, x_1, and x_2. P94A3Dist is ordinary Euclidean
  distance.

  C ranges over every total function from this triangle to the four-element
  ordinal 4, which is bijective with Fin 4; colors are observed only through
  equality. This directly matches the Lean domain. It is also equivalent to
  Isabelle's plane-domain coloring restricted to the triangle: restriction
  gives one direction, and every triangle coloring extends to the plane
  because the color carrier is nonempty. The two point witnesses remain
  internally existentially quantified.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P94A3I P94A3R2 P94A3Triangle P94A3Dist $.

p94a3-index-syntax $a class P94A3I $.
p94a3-plane-syntax $a class P94A3R2 $.
p94a3-triangle-syntax $a class P94A3Triangle $.
p94a3-distance-syntax $a class ( P94A3Dist A B ) $.

p94a3-index-definition $a |- P94A3I = ( 1 ... 2 ) $.

p94a3-plane-definition $a |- P94A3R2 = ( RR ^m P94A3I ) $.

p94a3-triangle-definition $a |- P94A3Triangle = {
  x e. P94A3R2 |
  (
    0 <_ ( x ` 1 )
    /\
    (
      0 <_ ( x ` 2 )
      /\
      ( ( x ` 1 ) + ( x ` 2 ) ) <_ 1
    )
  )
} $.

${
  $d A B k $.

  p94a3-distance-definition $a |- (
    P94A3Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P94A3I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d C p q $.

  putnambench-putnam-1994-a3 $a |-
    A. C e. ( 4 ^m P94A3Triangle )
      E. p e. P94A3Triangle E. q e. P94A3Triangle
        (
          ( C ` p ) = ( C ` q )
          /\
          ( 2 - ( sqrt ` 2 ) ) <_ ( P94A3Dist p q )
        )
  $.
$}
