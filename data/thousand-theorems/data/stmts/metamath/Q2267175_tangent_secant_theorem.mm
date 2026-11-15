$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2267175
  (thousand-theorems__metamath__Q2267175), "Tangent-secant theorem": in an
  arbitrary real inner-product affine space, the squared distance from a
  point to a tangent point of a sphere equals the product of its distances
  to two sphere points on a secant line. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by SetMM
  CPreHil structures whose scalar field is RRfld. Choosing an affine origin
  identifies the source normed affine torsor with this vector presentation
  while preserving differences, distances, affine lines, spheres, and
  orthogonality.

  W Q2267175Dist A B is the norm distance from A to B. W Q2267175Line A B P
  says that P lies in the affine span of A and B. W Q2267175Sphere O R is
  the sphere record with center O and arbitrary real radius R, represented
  by its membership set.

  W Q2267175Tangent O R T P states that T lies on that sphere and the
  direction from T to P is orthogonal to the radius from O to T. For the
  affine line through P and T, this is equivalent to the source structure
  IsTangentAt: T belongs to the sphere and line, and the whole line lies in
  the affine hyperplane through T orthogonal to the radius.

  Every declaration before the final one is syntax or an explicit
  bidirectional definition. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c Q2267175Dist Q2267175Line Q2267175Sphere Q2267175Tangent $.

q2267175-distance-syntax $a class ( W Q2267175Dist A B ) $.
q2267175-line-syntax $a wff ( W Q2267175Line A B P ) $.
q2267175-sphere-syntax $a class ( W Q2267175Sphere O R ) $.
q2267175-tangent-syntax
  $a wff ( W Q2267175Tangent O R T P ) $.

q2267175-distance-definition $a |- (
  W Q2267175Dist A B
) = (
  ( norm ` W ) ` ( B ( -g ` W ) A )
) $.

${
  $d A B P W x $.

  q2267175-line-definition $a |- (
    ( W Q2267175Line A B P )
    <->
    E. x e. RR
      P
      =
      (
        ( x ( .s ` W ) A )
        ( +g ` W )
        ( ( 1 - x ) ( .s ` W ) B )
      )
  ) $.
$}

${
  $d O R W X $.

  q2267175-sphere-definition $a |- (
    W Q2267175Sphere O R
  ) = {
    X e. ( Base ` W ) |
      ( W Q2267175Dist X O ) = R
  } $.
$}

q2267175-tangent-definition $a |- (
  ( W Q2267175Tangent O R T P )
  <->
  (
    T e. ( W Q2267175Sphere O R )
    /\
    (
      (
        ( P ( -g ` W ) T )
        ( .i ` W )
        ( T ( -g ` W ) O )
      )
      =
      0
    )
  )
) $.

${
  $d A B O P R T W $.

  thousand-theorems-q2267175-tangent-secant $a |- A. W
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
              A. T e. ( Base ` W )
                A. P e. ( Base ` W )
                  (
                    (
                      A e. ( W Q2267175Sphere O R )
                      /\
                      (
                        B e. ( W Q2267175Sphere O R )
                        /\
                        (
                          ( W Q2267175Line A B P )
                          /\
                          ( W Q2267175Tangent O R T P )
                        )
                      )
                    )
                    ->
                    (
                      ( ( W Q2267175Dist P T ) ^ 2 )
                      =
                      (
                        ( W Q2267175Dist P A )
                        x.
                        ( W Q2267175Dist P B )
                      )
                    )
                  )
    )
  $.
$}
