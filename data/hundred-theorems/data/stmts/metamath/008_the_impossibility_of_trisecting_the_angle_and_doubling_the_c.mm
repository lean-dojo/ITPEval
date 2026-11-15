$(
  Statement-only formalization of "The Impossibility of Trisecting the Angle
  and Doubling the Cube" from Hundred Theorems item 008: straightedge-and-
  compass constructibility in the real plane, including the impossibility of
  constructing a real cube root of 2 and of trisecting a 60-degree angle.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  A point with real coordinates (u,v) is represented by the complex number
  u + i*v.  The class HundredConstr008 is defined as the intersection of all
  subsets s of the complex plane that contain every rational-coordinate point
  and are closed under line-line, line-circle, and distinct-circle
  intersections.  Thus the quantifier over s ranges over every plane subset,
  giving exactly the least closure used by the HOL Light and Isabelle
  constructibility definitions.

  Lines are parametrized over RR.  Circle radii are distances between already
  constructible points.  The imaginary-part determinant is nonzero exactly
  when two line directions are nonparallel.  The final declarations are
  unproved $a statements, following the corpus convention for Metamath
  statement artifacts.
$)

$c HundredConstr008 $.

chundredconstr008 $a class HundredConstr008 $.

${
  $d a b c d e f r s t x y z $.

  df-hundredconstr008 $a |- HundredConstr008 = { z e. CC | A. s (
    (
      (
        s C_ CC
        /\
        A. x e. QQ A. y e. QQ
          ( x + ( _i x. y ) ) e. s
      )
      /\
      A. x e. CC
      (
        (
          E. a e. s E. b e. s E. c e. s E. d e. s
          E. t e. RR E. r e. RR
          (
            x = ( a + ( t x. ( b - a ) ) )
            /\
            (
              x = ( c + ( r x. ( d - c ) ) )
              /\
              ( Im ` ( ( * ` ( b - a ) ) x. ( d - c ) ) ) =/= 0
            )
          )
          \/
          E. a e. s E. b e. s E. c e. s E. d e. s E. e e. s
          E. t e. RR
          (
            a =/= b
            /\
            (
              x = ( a + ( t x. ( b - a ) ) )
              /\
              ( abs ` ( x - c ) ) = ( abs ` ( d - e ) )
            )
          )
          \/
          E. a e. s E. b e. s E. c e. s
          E. d e. s E. e e. s E. f e. s
          (
            -.
            (
              a = d
              /\
              ( abs ` ( b - c ) ) = ( abs ` ( e - f ) )
            )
            /\
            (
              ( abs ` ( x - a ) ) = ( abs ` ( b - c ) )
              /\
              ( abs ` ( x - d ) ) = ( abs ` ( e - f ) )
            )
          )
        )
        ->
        x e. s
      )
    )
    ->
    z e. s
  ) } $.
$}

$(
  Under the coordinate identification above, x is the source point (x,0),
  while cos(pi/9) + i*y is the source point (cos(pi/9),y).  The first
  trisection assertion is the Isabelle conclusion; the second is the stronger
  HOL Light conclusion for every real ordinate.
$)

hundred-doubling-cube-008 $a |- A. x e. RR
  ( ( x ^ 3 ) = 2 -> x e/ HundredConstr008 ) $.

hundred-trisect-sixty-axis-008 $a |-
  ( cos ` ( _pi / 9 ) ) e/ HundredConstr008 $.

hundred-trisect-sixty-any-ordinate-008 $a |- A. y e. RR
  ( ( ( cos ` ( _pi / 9 ) ) + ( _i x. y ) ) e/ HundredConstr008 ) $.
