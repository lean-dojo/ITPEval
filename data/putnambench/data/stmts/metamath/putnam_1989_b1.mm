$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_b1: the area probability that a point in the unit square is
  nearer its center than every boundary point, expressed in normalized
  quadratic-irrational form. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P89B1R2 is the real coordinate plane on the index set {1,2}.
  P89B1Square is the closed unit square, P89B1Boundary is its four-edge
  boundary, and P89B1Center is the constant coordinate function 1/2.
  P89B1Dist is Euclidean distance and P89B1Closer is the set of square
  points strictly nearer the center than every boundary point.

  P89B1Area is planar Lebesgue measure through set.mm's finite-dimensional
  volume function voln. P89B1Solution is the annotated source quadruple
  (4,2,-5,3). P89B1Normalized states positivity of b and d, that b is not
  an integer square, and gcd(a,c,d) = 1.

  The final unproved $a assertion states the normalization conditions and
  the exact ratio of the two planar areas. The definitions eliminate the
  source parameters constrained by square_def, perimeter_def, center_def,
  and hScloser. This root file declares no $p proof statement; the included
  set.mm library supplies the standard mathematical vocabulary.
$)

$c P89B1I P89B1R2 P89B1Square P89B1Boundary P89B1Center $.
$c P89B1Dist P89B1Closer P89B1Area $.
$c P89B1A P89B1B P89B1C P89B1D P89B1Solution P89B1Normalized $.

p89b1-index-syntax $a class P89B1I $.
p89b1-plane-syntax $a class P89B1R2 $.
p89b1-square-syntax $a class P89B1Square $.
p89b1-boundary-syntax $a class P89B1Boundary $.
p89b1-center-syntax $a class P89B1Center $.
p89b1-distance-syntax $a class ( P89B1Dist p q ) $.
p89b1-closer-syntax $a class P89B1Closer $.
p89b1-area-syntax $a class ( P89B1Area A ) $.
p89b1-a-syntax $a class P89B1A $.
p89b1-b-syntax $a class P89B1B $.
p89b1-c-syntax $a class P89B1C $.
p89b1-d-syntax $a class P89B1D $.
p89b1-solution-syntax $a class P89B1Solution $.
p89b1-normalized-syntax $a wff P89B1Normalized $.

p89b1-index-definition $a |- P89B1I = ( 1 ... 2 ) $.

p89b1-plane-definition $a |- P89B1R2 = ( RR ^m P89B1I ) $.

${
  $d j p $.

  p89b1-square-definition $a |- P89B1Square = {
    p e. P89B1R2 |
    A. j e. P89B1I
      (
        0 <_ ( p ` j )
        /\
        ( p ` j ) <_ 1
      )
  } $.
$}

${
  p89b1-boundary-definition $a |- P89B1Boundary = {
    p e. P89B1Square |
    (
      ( p ` 1 ) = 0
      \/
      (
        ( p ` 1 ) = 1
        \/
        (
          ( p ` 2 ) = 0
          \/
          ( p ` 2 ) = 1
        )
      )
    )
  } $.
$}

p89b1-center-definition $a |- P89B1Center =
  ( j e. P89B1I |-> ( 1 / 2 ) ) $.

${
  $d j p q $.

  p89b1-distance-definition $a |- (
    P89B1Dist p q
  ) = (
    sqrt
    `
    (
      sum_ j e. P89B1I
        ( ( ( p ` j ) - ( q ` j ) ) ^ 2 )
    )
  ) $.
$}

${
  $d p q $.

  p89b1-closer-definition $a |- P89B1Closer = {
    p e. P89B1Square |
    A. q e. P89B1Boundary
      ( P89B1Dist p P89B1Center )
      <
      ( P89B1Dist p q )
  } $.
$}

p89b1-area-definition $a |- (
  P89B1Area A
) = (
  ( voln ` P89B1I ) ` A
) $.

p89b1-a-definition $a |- P89B1A = 4 $.
p89b1-b-definition $a |- P89B1B = 2 $.
p89b1-c-definition $a |- P89B1C = ( -u 5 ) $.
p89b1-d-definition $a |- P89B1D = 3 $.

p89b1-solution-definition $a |- P89B1Solution =
  <.
    P89B1A
    ,
    <.
      P89B1B
      ,
      <. P89B1C , P89B1D >.
    >.
  >. $.

${
  p89b1-normalized-definition $a |- (
    P89B1Normalized
    <->
    (
      0 < P89B1B
      /\
      (
        0 < P89B1D
        /\
        (
          -. E. n e. ZZ ( n ^ 2 ) = P89B1B
          /\
          ( ( P89B1A gcd P89B1C ) gcd P89B1D ) = 1
        )
      )
    )
  ) $.
$}

putnambench-putnam-1989-b1 $a |- (
  P89B1Normalized
  /\
  (
    ( P89B1Area P89B1Closer )
    /
    ( P89B1Area P89B1Square )
  )
  =
  (
    (
      ( P89B1A x. ( sqrt ` P89B1B ) )
      +
      P89B1C
    )
    /
    P89B1D
  )
) $.
