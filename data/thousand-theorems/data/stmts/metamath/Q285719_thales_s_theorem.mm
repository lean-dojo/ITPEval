$(
  Statement-only formalization of Thousand Theorems corpus artifact Q285719
  (thousand-theorems__metamath__Q285719), "Thales's theorem": in an arbitrary
  real inner-product affine space, if two points are diameter endpoints of a
  sphere, then the angle they subtend at a third point is a right angle if
  and only if that third point lies on the sphere. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by SetMM
  CPreHil structures whose scalar field is RRfld. Choosing any point as an
  affine origin identifies the source's normed affine torsor with this vector
  presentation while preserving spheres, midpoints, distances, and angles.

  W Q285719Ray A B is the vector from B to A, W Q285719Dist A B is its norm,
  and W Q285719Angle A B C is the total unoriented angle at B. When either
  ray is zero, the angle is pi/2, matching the source convention; otherwise
  it is the arccosine of the normalized inner product.

  W Q285719Sphere O R is the sphere with center O and radius R.
  W Q285719Mid A C is the affine midpoint of A and C, and
  W Q285719IsDiameter O R A C says that A lies on that sphere and the
  midpoint of A and C is O. This is exactly the source Sphere.IsDiameter
  structure with the sphere record represented by its center-radius pair;
  C's membership follows from the equal distances to the midpoint.

  Every declaration before the final one is syntax or an explicit
  definition. The final $a declaration is the single unproved corpus
  statement, and the database contains no $p proof statement.
$)

$c
  Q285719Ray Q285719Dist Q285719Angle
  Q285719Sphere Q285719Mid Q285719IsDiameter
$.

q285719-ray-syntax $a class ( W Q285719Ray A B ) $.
q285719-distance-syntax $a class ( W Q285719Dist A B ) $.
q285719-angle-syntax $a class ( W Q285719Angle A B C ) $.
q285719-sphere-syntax $a class ( W Q285719Sphere O R ) $.
q285719-midpoint-syntax $a class ( W Q285719Mid A C ) $.
q285719-is-diameter-syntax
  $a wff ( W Q285719IsDiameter O R A C ) $.

q285719-ray-definition $a |- (
  W Q285719Ray A B
) = (
  A ( -g ` W ) B
) $.

q285719-distance-definition $a |- (
  W Q285719Dist A B
) = (
  ( norm ` W ) ` ( W Q285719Ray A B )
) $.

q285719-angle-definition $a |- (
  W Q285719Angle A B C
) = if (
  (
    ( ( W Q285719Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q285719Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q285719Ray A B )
        ( .i ` W )
        ( W Q285719Ray C B )
      )
      /
      (
        ( W Q285719Dist A B )
        x.
        ( W Q285719Dist C B )
      )
    )
  )
) $.

${
  $d O R W X $.

  q285719-sphere-definition $a |- (
    W Q285719Sphere O R
  ) = {
    X e. ( Base ` W ) |
      ( W Q285719Dist X O ) = R
  } $.
$}

q285719-midpoint-definition $a |- (
  W Q285719Mid A C
) = (
  ( 1 / 2 )
  ( .s ` W )
  ( A ( +g ` W ) C )
) $.

q285719-is-diameter-definition $a |- (
  ( W Q285719IsDiameter O R A C )
  <->
  (
    A e. ( W Q285719Sphere O R )
    /\
    ( W Q285719Mid A C ) = O
  )
) $.

${
  $d A B C O R W $.

  thousand-theorems-q285719-thales-theorem $a |- A. W
    (
      (
        W e. CPreHil
        /\
        ( Scalar ` W ) = RRfld
      )
      ->
      A. O e. ( Base ` W )
        A. R e. RR
          A. A e. ( Base ` W )
            A. B e. ( Base ` W )
              A. C e. ( Base ` W )
                (
                  ( W Q285719IsDiameter O R A C )
                  ->
                  (
                    (
                      ( W Q285719Angle A B C )
                      =
                      ( _pi / 2 )
                    )
                    <->
                    B e. ( W Q285719Sphere O R )
                  )
                )
    )
  $.
$}
