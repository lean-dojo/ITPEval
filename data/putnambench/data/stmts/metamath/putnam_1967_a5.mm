$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_a5: every convex region in the real Euclidean plane with
  Lebesgue area greater than pi / 4 contains two points exactly one unit
  apart. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P67A5R2 is the real coordinate plane. P67A5Dist is Euclidean distance,
  P67A5Convex expands real convexity coordinatewise, and P67A5Area is
  two-dimensional Lebesgue measure via set.mm's finite-dimensional volume
  function voln.

  The final declaration is the single unproved $a corpus statement. It
  preserves the arbitrary region and the internally existential pair of
  points; this database contains no $p proof statement.
$)

$c P67A5I P67A5R2 P67A5Dist P67A5Convex P67A5Area $.

p67a5-index-syntax $a class P67A5I $.
p67a5-plane-syntax $a class P67A5R2 $.
p67a5-distance-syntax $a class ( P67A5Dist A B ) $.
p67a5-convex-syntax $a wff ( P67A5Convex A ) $.
p67a5-area-syntax $a class ( P67A5Area A ) $.

p67a5-index-definition $a |- P67A5I = ( 1 ... 2 ) $.

p67a5-plane-definition $a |- P67A5R2 = ( RR ^m P67A5I ) $.

${
  $d A B j $.

  p67a5-distance-definition $a |- (
    P67A5Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P67A5I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A j t x y $.

  p67a5-convex-definition $a |- (
    ( P67A5Convex A )
    <->
    (
      A C_ P67A5R2
      /\
      A. x e. A A. y e. A A. t e. ( 0 [,] 1 )
        (
          j e. P67A5I |->
            (
              ( ( 1 - t ) x. ( x ` j ) )
              +
              ( t x. ( y ` j ) )
            )
        )
        e. A
    )
  ) $.
$}

p67a5-area-definition $a |- (
  P67A5Area A
) = (
  ( voln ` P67A5I )
  `
  A
) $.

${
  $d P Q R $.

  putnambench-putnam-1967-a5 $a |- A. R
    (
      (
        ( P67A5Convex R )
        /\
        ( _pi / 4 ) < ( P67A5Area R )
      )
      ->
      E. P e. R E. Q e. R
        ( P67A5Dist P Q ) = 1
    )
  $.
$}
