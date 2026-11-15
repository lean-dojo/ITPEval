$(
  Statement-only formalization of Thousand Theorems corpus artifact Q739403
  (thousand-theorems__metamath__Q739403), "Stewart's theorem": in an arbitrary
  real inner-product affine space, four points with a straight angle at one
  point satisfy Stewart's distance identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by SetMM
  CPreHil structures whose scalar field has base RR. By the definition of
  CPreHil, its scalar field is the restriction of CCfld to that base, so this
  condition identifies it with RRfld by df-refld. The generalized real
  Euclidean spaces RR^ I satisfy these conditions by rrxcph and rrxsca, making
  the structure guard explicitly nonempty. Viewing the vector space as its
  canonical affine torsor preserves differences, distances, and angles.

  W Q739403Ray A B is the vector from B to A, W Q739403Dist A B is its norm,
  and W Q739403Angle A B C is the total unoriented angle at B. When either
  ray is zero, the angle is pi/2, matching the source convention; otherwise
  it is the arccosine of the normalized inner product.

  Every declaration before the final one is syntax or an explicit faithful
  definition. The final $a declaration is the single unproved corpus
  statement, and this database contains no $p proof statement.
$)

$c Q739403Ray Q739403Dist Q739403Angle $.

q739403-ray-syntax $a class ( W Q739403Ray A B ) $.
q739403-distance-syntax $a class ( W Q739403Dist A B ) $.
q739403-angle-syntax $a class ( W Q739403Angle A B C ) $.

q739403-ray-definition $a |- (
  W Q739403Ray A B
) = (
  A ( -g ` W ) B
) $.

q739403-distance-definition $a |- (
  W Q739403Dist A B
) = (
  ( norm ` W ) ` ( W Q739403Ray A B )
) $.

q739403-angle-definition $a |- (
  W Q739403Angle A B C
) = if (
  (
    ( ( W Q739403Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q739403Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q739403Ray A B )
        ( .i ` W )
        ( W Q739403Ray C B )
      )
      /
      (
        ( W Q739403Dist A B )
        x.
        ( W Q739403Dist C B )
      )
    )
  )
) $.

${
  $d A B C P W $.

  thousand-theorems-q739403-stewart $a |- A. W
    (
      (
        W e. CPreHil
        /\
        ( Base ` ( Scalar ` W ) ) = RR
      )
      ->
      A. A e. ( Base ` W )
        A. B e. ( Base ` W )
          A. C e. ( Base ` W )
            A. P e. ( Base ` W )
              (
                ( ( W Q739403Angle B P C ) = _pi )
                ->
                (
                  (
                    (
                      ( W Q739403Dist A B ) ^ 2
                    )
                    x.
                    ( W Q739403Dist C P )
                  )
                  +
                  (
                    (
                      ( W Q739403Dist A C ) ^ 2
                    )
                    x.
                    ( W Q739403Dist B P )
                  )
                )
                =
                (
                  ( W Q739403Dist B C )
                  x.
                  (
                    (
                      ( W Q739403Dist A P ) ^ 2
                    )
                    +
                    (
                      ( W Q739403Dist B P )
                      x.
                      ( W Q739403Dist C P )
                    )
                  )
                )
              )
    )
  $.
$}
