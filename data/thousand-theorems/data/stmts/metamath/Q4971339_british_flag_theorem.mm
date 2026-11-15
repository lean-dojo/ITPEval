$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4971339
  (thousand-theorems__metamath__Q4971339), "British flag theorem": in an
  arbitrary real inner-product affine space, a possibly degenerate
  parallelogram with a right angle satisfies the opposite-corner
  squared-distance identity for every point. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces. The predicate
  W Q4971339RealInnerProductSpace explicitly requires a generalized
  pre-Hilbert structure over RRfld, the normed-module laws, and the defining
  equality between the norm and the square root of the self inner product.
  It is therefore the SetMM rendering of the source NormedAddCommGroup and
  InnerProductSpace real typeclass package, without a finite-dimensionality
  restriction. Choosing any affine origin identifies the source's normed
  affine torsor with Base ` W while preserving distances, angles, and
  equality of affine midpoints.

  W Q4971339Ray A B is the vector from B to A, W Q4971339Dist A B is its
  norm, and W Q4971339Angle A B C is the total unoriented angle at B. When
  either ray is zero, the angle is pi/2, matching the source convention;
  otherwise it is the arccosine of the normalized inner product.
  W Q4971339Mid A C is the affine midpoint of A and C. Thus equality of the
  midpoints of A,C and B,D is exactly the source's parallelogram hypothesis.

  Every declaration before the final one is syntax or an explicit definition.
  The final $a declaration is the single unproved corpus statement, and this
  database contains no $p proof statement.
$)

$c Q4971339RealInnerProductSpace
   Q4971339Ray Q4971339Dist Q4971339Angle Q4971339Mid $.

q4971339-real-inner-product-space-syntax
  $a wff ( W Q4971339RealInnerProductSpace ) $.
q4971339-ray-syntax $a class ( W Q4971339Ray A B ) $.
q4971339-distance-syntax $a class ( W Q4971339Dist A B ) $.
q4971339-angle-syntax $a class ( W Q4971339Angle A B C ) $.
q4971339-midpoint-syntax $a class ( W Q4971339Mid A C ) $.

${
  $d W x $.

  q4971339-real-inner-product-space-definition $a |- (
    ( W Q4971339RealInnerProductSpace )
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

q4971339-ray-definition $a |- (
  W Q4971339Ray A B
) = (
  A ( -g ` W ) B
) $.

q4971339-distance-definition $a |- (
  W Q4971339Dist A B
) = (
  ( norm ` W ) ` ( W Q4971339Ray A B )
) $.

q4971339-angle-definition $a |- (
  W Q4971339Angle A B C
) = if (
  (
    ( ( W Q4971339Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q4971339Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q4971339Ray A B )
        ( .i ` W )
        ( W Q4971339Ray C B )
      )
      /
      (
        ( W Q4971339Dist A B )
        x.
        ( W Q4971339Dist C B )
      )
    )
  )
) $.

q4971339-midpoint-definition $a |- (
  W Q4971339Mid A C
) = (
  ( 1 / 2 )
  ( .s ` W )
  ( A ( +g ` W ) C )
) $.

${
  $d A B C D P W $.

  thousand-theorems-q4971339-british-flag-theorem $a |- A. W
    (
      ( W Q4971339RealInnerProductSpace )
      ->
      A. A e. ( Base ` W )
        A. B e. ( Base ` W )
          A. C e. ( Base ` W )
            A. D e. ( Base ` W )
              A. P e. ( Base ` W )
                (
                  (
                    (
                      ( W Q4971339Mid A C )
                      =
                      ( W Q4971339Mid B D )
                    )
                    /\
                    (
                      ( W Q4971339Angle B A D )
                      =
                      ( _pi / 2 )
                    )
                  )
                  ->
                  (
                    (
                      ( ( W Q4971339Dist P A ) ^ 2 )
                      +
                      ( ( W Q4971339Dist P C ) ^ 2 )
                    )
                    =
                    (
                      ( ( W Q4971339Dist P B ) ^ 2 )
                      +
                      ( ( W Q4971339Dist P D ) ^ 2 )
                    )
                  )
                )
    )
  $.
$}
