$(
  Statement-only formalization of Thousand Theorems corpus artifact Q11518
  (thousand-theorems__metamath__Q11518), "Pythagorean theorem": in an
  arbitrary real inner-product affine space, the squared-distance identity
  for three points holds if and only if the angle at the second point is a
  right angle. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by SetMM
  CPreHil structures whose scalar field is RRfld. Choosing any point as an
  affine origin identifies the source's normed affine torsor with this vector
  presentation while preserving all distances and angles.

  W Q11518Ray A B is the vector from B to A, W Q11518Dist A B is its norm,
  and W Q11518Angle A B C is the total unoriented angle at B. When either ray
  is zero, the angle is pi/2, matching the source convention; otherwise it is
  the arccosine of the normalized inner product.

  Squaring with ^ 2 is equivalent over the reals to the source's explicit
  self-products. Every declaration before the final one is syntax or an
  explicit definition. The final $a declaration is the single unproved corpus
  statement, and the database contains no $p proof statement.
$)

$c Q11518Ray Q11518Dist Q11518Angle $.

q11518-ray-syntax $a class ( W Q11518Ray A B ) $.
q11518-distance-syntax $a class ( W Q11518Dist A B ) $.
q11518-angle-syntax $a class ( W Q11518Angle A B C ) $.

q11518-ray-definition $a |- (
  W Q11518Ray A B
) = (
  A ( -g ` W ) B
) $.

q11518-distance-definition $a |- (
  W Q11518Dist A B
) = (
  ( norm ` W ) ` ( W Q11518Ray A B )
) $.

q11518-angle-definition $a |- (
  W Q11518Angle A B C
) = if (
  (
    ( ( W Q11518Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q11518Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q11518Ray A B )
        ( .i ` W )
        ( W Q11518Ray C B )
      )
      /
      (
        ( W Q11518Dist A B )
        x.
        ( W Q11518Dist C B )
      )
    )
  )
) $.

${
  $d A B C W $.

  thousand-theorems-q11518-pythagorean-theorem $a |- A. W
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
            (
              (
                ( ( W Q11518Dist A C ) ^ 2 )
                =
                (
                  ( ( W Q11518Dist A B ) ^ 2 )
                  +
                  ( ( W Q11518Dist C B ) ^ 2 )
                )
              )
              <->
              (
                ( W Q11518Angle A B C )
                =
                ( _pi / 2 )
              )
            )
    )
  $.
$}
