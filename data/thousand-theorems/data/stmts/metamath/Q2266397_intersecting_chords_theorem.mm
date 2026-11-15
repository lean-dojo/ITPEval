$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2266397
  (thousand-theorems__metamath__Q2266397), "Intersecting chords theorem":
  in an arbitrary real inner-product affine space, two straight chords
  through four cospherical points have equal products of distances from
  their common point. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces. The predicate
  W Q2266397RealInnerProductSpace explicitly requires a generalized
  pre-Hilbert structure over RRfld, the normed-module laws, and the defining
  equality between the norm and the square root of the self inner product.
  It is therefore the SetMM rendering of the source NormedAddCommGroup and
  InnerProductSpace real typeclass package, without a finite-dimensionality
  restriction. Choosing the common point P as an affine origin identifies
  the source normed affine torsor with this vector presentation while
  preserving differences, distances, angles, and spheres.

  W Q2266397Ray A B is the vector from B to A, W Q2266397Dist A B is its
  norm, and W Q2266397Angle A B C is the total unoriented angle at B. When
  either ray is zero, the angle is pi/2, matching the source convention;
  otherwise it is the arccosine of the normalized inner product.

  W Q2266397Cospherical A B C D states that the four points have a common
  center and a common nonnegative real distance from it. This is equivalent
  to the source predicate Cospherical {A, B, C, D}.

  Every declaration before the final one is syntax or an explicit
  bidirectional definition. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c
  Q2266397RealInnerProductSpace
  Q2266397Ray Q2266397Dist Q2266397Angle Q2266397Cospherical
$.

q2266397-real-inner-product-space-syntax
  $a wff ( W Q2266397RealInnerProductSpace ) $.
q2266397-ray-syntax $a class ( W Q2266397Ray A B ) $.
q2266397-distance-syntax $a class ( W Q2266397Dist A B ) $.
q2266397-angle-syntax $a class ( W Q2266397Angle A B C ) $.
q2266397-cospherical-syntax
  $a wff ( W Q2266397Cospherical A B C D ) $.

${
  $d W x $.

  q2266397-real-inner-product-space-definition $a |- (
    ( W Q2266397RealInnerProductSpace )
    <->
    (
      (
        W e. PreHil
        /\
        W e. NrmMod
      )
      /\
      (
        ( Scalar ` W ) = RRfld
        /\
        (
          ( norm ` W )
          =
          (
            x e. ( Base ` W ) |->
              ( sqrt ` ( x ( .i ` W ) x ) )
          )
        )
      )
    )
  ) $.
$}

q2266397-ray-definition $a |- (
  W Q2266397Ray A B
) = (
  A ( -g ` W ) B
) $.

q2266397-distance-definition $a |- (
  W Q2266397Dist A B
) = (
  ( norm ` W ) ` ( W Q2266397Ray A B )
) $.

q2266397-angle-definition $a |- (
  W Q2266397Angle A B C
) = if (
  (
    ( ( W Q2266397Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q2266397Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q2266397Ray A B )
        ( .i ` W )
        ( W Q2266397Ray C B )
      )
      /
      (
        ( W Q2266397Dist A B )
        x.
        ( W Q2266397Dist C B )
      )
    )
  )
) $.

${
  $d A B C D O R W $.

  q2266397-cospherical-definition $a |- (
    ( W Q2266397Cospherical A B C D )
    <->
    E. O e. ( Base ` W )
      E. R e. RR
        (
          0 <_ R
          /\
          (
            ( ( W Q2266397Dist A O ) = R )
            /\
            (
              ( ( W Q2266397Dist B O ) = R )
              /\
              (
                ( ( W Q2266397Dist C O ) = R )
                /\
                ( ( W Q2266397Dist D O ) = R )
              )
            )
          )
        )
  ) $.
$}

${
  $d A B C D P W $.

  thousand-theorems-q2266397-intersecting-chords $a |- A. W
    (
      ( W Q2266397RealInnerProductSpace )
      ->
      A. A e. ( Base ` W )
        A. B e. ( Base ` W )
          A. C e. ( Base ` W )
            A. D e. ( Base ` W )
              A. P e. ( Base ` W )
                (
                  (
                    ( W Q2266397Cospherical A B C D )
                    /\
                    (
                      ( W Q2266397Angle A P B ) = _pi
                      /\
                      ( W Q2266397Angle C P D ) = _pi
                    )
                  )
                  ->
                  (
                    (
                      ( W Q2266397Dist A P )
                      x.
                      ( W Q2266397Dist B P )
                    )
                    =
                    (
                      ( W Q2266397Dist C P )
                      x.
                      ( W Q2266397Dist D P )
                    )
                  )
                )
    )
  $.
$}
