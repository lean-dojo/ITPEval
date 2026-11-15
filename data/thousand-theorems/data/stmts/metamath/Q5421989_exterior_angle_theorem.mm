$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5421989
  (thousand-theorems__metamath__Q5421989), "Exterior angle theorem": in an
  arbitrary real inner-product affine space, if one triangle vertex lies
  strictly between an exterior point and a second vertex, then the exterior
  angle equals the sum of the two opposite interior angles. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces. The predicate
  W Q5421989RealInnerProductSpace explicitly requires a generalized
  pre-Hilbert structure over RRfld, the normed-module laws, and the defining
  equality between the norm and the square root of the self inner product.
  It is therefore the SetMM rendering of the source NormedAddCommGroup and
  InnerProductSpace real typeclass package, without a finite-dimensionality
  restriction. Choosing any affine origin identifies the source normed affine
  torsor with Base ` W while preserving affine combinations and angles;
  conversely, Base ` W is such a torsor.

  W Q5421989Ray A B is the vector from B to A, and
  W Q5421989Dist A B is its norm. W Q5421989Angle A B C is the total
  unoriented angle at B: it is pi/2 when either ray is zero and otherwise is
  the arccosine of the normalized real inner product, matching the source
  angle convention.

  W Q5421989StrictBetween A B C says that B is distinct from both endpoints
  and is the affine combination (1-t)A+tC for a real t strictly between zero
  and one. Thus it exactly renders Sbtw RR A B C, including its endpoint
  strictness conditions.

  Every declaration before the final one is syntax or an explicit faithful
  definition. The final $a declaration is the single unproved corpus
  statement, and this database contains no $p proof statement.
$)

$c
  Q5421989RealInnerProductSpace
  Q5421989Ray Q5421989Dist Q5421989Angle Q5421989StrictBetween
$.

q5421989-real-inner-product-space-syntax
  $a wff ( W Q5421989RealInnerProductSpace ) $.
q5421989-ray-syntax
  $a class ( W Q5421989Ray A B ) $.
q5421989-distance-syntax
  $a class ( W Q5421989Dist A B ) $.
q5421989-angle-syntax
  $a class ( W Q5421989Angle A B C ) $.
q5421989-strict-between-syntax
  $a wff ( W Q5421989StrictBetween A B C ) $.

${
  $d W x $.

  q5421989-real-inner-product-space-definition $a |- (
    ( W Q5421989RealInnerProductSpace )
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

q5421989-ray-definition $a |- (
  W Q5421989Ray A B
) = (
  A ( -g ` W ) B
) $.

q5421989-distance-definition $a |- (
  W Q5421989Dist A B
) = (
  ( norm ` W ) ` ( W Q5421989Ray A B )
) $.

q5421989-angle-definition $a |- (
  W Q5421989Angle A B C
) = if (
  (
    ( ( W Q5421989Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q5421989Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q5421989Ray A B )
        ( .i ` W )
        ( W Q5421989Ray C B )
      )
      /
      (
        ( W Q5421989Dist A B )
        x.
        ( W Q5421989Dist C B )
      )
    )
  )
) $.

${
  $d A B C W t $.

  q5421989-strict-between-definition $a |- (
    ( W Q5421989StrictBetween A B C )
    <->
    (
      ( B =/= A /\ B =/= C )
      /\
      E. t e. ( 0 (,) 1 )
        B
        =
        (
          ( ( 1 - t ) ( .s ` W ) A )
          ( +g ` W )
          ( t ( .s ` W ) C )
        )
    )
  ) $.
$}

${
  $d a b c d w $.

  thousand-theorems-q5421989-exterior-angle-theorem $a |- A. w
    (
      ( w Q5421989RealInnerProductSpace )
      ->
      A. a e. ( Base ` w )
        A. b e. ( Base ` w )
          A. c e. ( Base ` w )
            A. d e. ( Base ` w )
              (
                ( w Q5421989StrictBetween a b c )
                ->
                (
                  ( w Q5421989Angle d b a )
                  =
                  (
                    ( w Q5421989Angle b d c )
                    +
                    ( w Q5421989Angle d c b )
                  )
                )
              )
    )
  $.
$}
