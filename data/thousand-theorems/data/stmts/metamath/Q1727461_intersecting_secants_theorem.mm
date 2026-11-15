$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1727461
  (thousand-theorems__metamath__Q1727461), "Intersecting secants theorem":
  in an arbitrary real inner-product affine space, two zero-angle secants
  through four cospherical points have equal products of distances from
  their common point. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces. The predicate
  W Q1727461RealInnerProductSpace explicitly requires a generalized
  pre-Hilbert structure over RRfld, the normed-module laws, and the defining
  equality between the norm and the square root of the self inner product.
  It is therefore the SetMM rendering of the source NormedAddCommGroup and
  InnerProductSpace real typeclass package, without a finite-dimensionality
  restriction. Choosing the common point P as an affine origin identifies
  the source normed affine torsor with this vector presentation while
  preserving differences, distances, angles, and spheres.

  W Q1727461Ray A B is the vector from B to A, W Q1727461Dist A B is its
  norm, and W Q1727461Angle A B C is the total unoriented angle at B. When
  either ray is zero, the angle is pi/2, matching the source convention;
  otherwise it is the arccosine of the normalized inner product.

  W Q1727461Cospherical A B C D states that the four points have a common
  center and a common nonnegative real distance from it. This is equivalent
  to the source predicate Cospherical {A, B, C, D}.

  Every declaration before the final one is syntax or an explicit
  bidirectional definition. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c
  Q1727461RealInnerProductSpace
  Q1727461Ray Q1727461Dist Q1727461Angle Q1727461Cospherical
$.

q1727461-real-inner-product-space-syntax
  $a wff ( W Q1727461RealInnerProductSpace ) $.
q1727461-ray-syntax $a class ( W Q1727461Ray A B ) $.
q1727461-distance-syntax $a class ( W Q1727461Dist A B ) $.
q1727461-angle-syntax $a class ( W Q1727461Angle A B C ) $.
q1727461-cospherical-syntax
  $a wff ( W Q1727461Cospherical A B C D ) $.

${
  $d W x $.

  q1727461-real-inner-product-space-definition $a |- (
    ( W Q1727461RealInnerProductSpace )
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

q1727461-ray-definition $a |- (
  W Q1727461Ray A B
) = (
  A ( -g ` W ) B
) $.

q1727461-distance-definition $a |- (
  W Q1727461Dist A B
) = (
  ( norm ` W ) ` ( W Q1727461Ray A B )
) $.

q1727461-angle-definition $a |- (
  W Q1727461Angle A B C
) = if (
  (
    ( ( W Q1727461Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q1727461Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q1727461Ray A B )
        ( .i ` W )
        ( W Q1727461Ray C B )
      )
      /
      (
        ( W Q1727461Dist A B )
        x.
        ( W Q1727461Dist C B )
      )
    )
  )
) $.

${
  $d A B C D O R W $.

  q1727461-cospherical-definition $a |- (
    ( W Q1727461Cospherical A B C D )
    <->
    E. O e. ( Base ` W )
      E. R e. RR
        (
          0 <_ R
          /\
          (
            ( ( W Q1727461Dist A O ) = R )
            /\
            (
              ( ( W Q1727461Dist B O ) = R )
              /\
              (
                ( ( W Q1727461Dist C O ) = R )
                /\
                ( ( W Q1727461Dist D O ) = R )
              )
            )
          )
        )
  ) $.
$}

${
  $d A B C D P W $.

  thousand-theorems-q1727461-intersecting-secants $a |- A. W
    (
      ( W Q1727461RealInnerProductSpace )
      ->
      A. A e. ( Base ` W )
        A. B e. ( Base ` W )
          A. C e. ( Base ` W )
            A. D e. ( Base ` W )
              A. P e. ( Base ` W )
                (
                  (
                    ( W Q1727461Cospherical A B C D )
                    /\
                    (
                      A =/= B
                      /\
                      (
                        C =/= D
                        /\
                        (
                          ( W Q1727461Angle A P B ) = 0
                          /\
                          ( W Q1727461Angle C P D ) = 0
                        )
                      )
                    )
                  )
                  ->
                  (
                    (
                      ( W Q1727461Dist A P )
                      x.
                      ( W Q1727461Dist B P )
                    )
                    =
                    (
                      ( W Q1727461Dist C P )
                      x.
                      ( W Q1727461Dist D P )
                    )
                  )
                )
    )
  $.
$}
