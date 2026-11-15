$(
  Statement-only formalization of Thousand Theorems corpus artifact Q459547
  (thousand-theorems__metamath__Q459547), "Ptolemy's theorem": in an
  arbitrary real inner-product affine space, four cospherical points whose
  diagonals form straight angles at a point satisfy Ptolemy's distance
  identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by SetMM
  CPreHil structures whose scalar field is RRfld. Choosing the source point P
  as an affine origin identifies its normed affine torsor with this vector
  presentation while preserving differences, distances, angles, and spheres.

  W Q459547Ray A B is the vector from B to A, W Q459547Dist A B is its norm,
  and W Q459547Angle A B C is the total unoriented angle at B. When either
  ray is zero, the angle is pi/2, matching the source convention; otherwise
  it is the arccosine of the normalized inner product.

  W Q459547Cospherical A B C D states that the four points have a common
  center and a common nonnegative real distance from it. This is equivalent
  to Cospherical {A, B, C, D}; nonnegativity follows from any of the four
  distance equalities and is made explicit here.

  Every declaration before the final one is syntax or an explicit
  bidirectional definition. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c Q459547Ray Q459547Dist Q459547Angle Q459547Cospherical $.

q459547-ray-syntax $a class ( W Q459547Ray A B ) $.
q459547-distance-syntax $a class ( W Q459547Dist A B ) $.
q459547-angle-syntax $a class ( W Q459547Angle A B C ) $.
q459547-cospherical-syntax
  $a wff ( W Q459547Cospherical A B C D ) $.

q459547-ray-definition $a |- (
  W Q459547Ray A B
) = (
  A ( -g ` W ) B
) $.

q459547-distance-definition $a |- (
  W Q459547Dist A B
) = (
  ( norm ` W ) ` ( W Q459547Ray A B )
) $.

q459547-angle-definition $a |- (
  W Q459547Angle A B C
) = if (
  (
    ( ( W Q459547Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q459547Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q459547Ray A B )
        ( .i ` W )
        ( W Q459547Ray C B )
      )
      /
      (
        ( W Q459547Dist A B )
        x.
        ( W Q459547Dist C B )
      )
    )
  )
) $.

${
  $d A B C D O R W $.

  q459547-cospherical-definition $a |- (
    ( W Q459547Cospherical A B C D )
    <->
    E. O e. ( Base ` W )
      E. R e. RR
        (
          0 <_ R
          /\
          (
            ( ( W Q459547Dist A O ) = R )
            /\
            (
              ( ( W Q459547Dist B O ) = R )
              /\
              (
                ( ( W Q459547Dist C O ) = R )
                /\
                ( ( W Q459547Dist D O ) = R )
              )
            )
          )
        )
  ) $.
$}

${
  $d A B C D P W $.

  thousand-theorems-q459547-ptolemy $a |- A. W
    (
      (
        W e. CPreHil
        /\
        ( Scalar ` W ) = RRfld
      )
      ->
      A. A e. ( Base ` W )
        A. B e. ( Base ` W )
          A. C e. ( Base ` W )
            A. D e. ( Base ` W )
              A. P e. ( Base ` W )
                (
                  (
                    ( W Q459547Cospherical A B C D )
                    /\
                    (
                      ( W Q459547Angle A P C ) = _pi
                      /\
                      ( W Q459547Angle B P D ) = _pi
                    )
                  )
                  ->
                  (
                    (
                      ( W Q459547Dist A B )
                      x.
                      ( W Q459547Dist C D )
                    )
                    +
                    (
                      ( W Q459547Dist B C )
                      x.
                      ( W Q459547Dist D A )
                    )
                  )
                  =
                  (
                    ( W Q459547Dist A C )
                    x.
                    ( W Q459547Dist B D )
                  )
                )
    )
  $.
$}
