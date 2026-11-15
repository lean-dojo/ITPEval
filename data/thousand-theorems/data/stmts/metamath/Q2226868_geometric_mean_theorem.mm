$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2226868
  (thousand-theorems__metamath__Q2226868), "Geometric mean theorem": in an
  arbitrary real inner-product affine space, if a point lies strictly between
  the endpoints of a right triangle's hypotenuse and is the foot of the
  perpendicular from the right-angle vertex, then the squared altitude equals
  the product of the two hypotenuse segments. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by SetMM
  CPreHil structures whose scalar field is RRfld. Choosing any point as an
  affine origin identifies the source normed affine torsor with this vector
  presentation while preserving affine combinations, distances, and angles.

  W Q2226868Ray A B is the vector from B to A, and W Q2226868Dist A B is its
  norm. W Q2226868Angle A B C is the source's total unoriented angle at B: it
  is pi/2 when either ray is zero and otherwise is the arccosine of the
  normalized real inner product.

  W Q2226868StrictBetween A B C says that B is distinct from both endpoints
  and is the affine combination (1-t)A+tC for a real t strictly between zero
  and one. Thus it exactly renders Sbtw RR A B C, including its endpoint
  strictness conditions.

  In the final assertion A, B, C, D correspond respectively to the source
  points p1, p2, p3, p4. Its three hypotheses and distance-product conclusion
  reproduce the complete proposition of the canonical Mathlib declaration.

  Every declaration before the final one is syntax or an explicit faithful
  definition. The final $a declaration is the single unproved corpus
  statement, and this database contains no $p proof statement.
$)

$c
  Q2226868Ray Q2226868Dist Q2226868Angle Q2226868StrictBetween
$.

q2226868-ray-syntax
  $a class ( W Q2226868Ray A B ) $.
q2226868-distance-syntax
  $a class ( W Q2226868Dist A B ) $.
q2226868-angle-syntax
  $a class ( W Q2226868Angle A B C ) $.
q2226868-strict-between-syntax
  $a wff ( W Q2226868StrictBetween A B C ) $.

q2226868-ray-definition $a |- (
  W Q2226868Ray A B
) = (
  A ( -g ` W ) B
) $.

q2226868-distance-definition $a |- (
  W Q2226868Dist A B
) = (
  ( norm ` W ) ` ( W Q2226868Ray A B )
) $.

q2226868-angle-definition $a |- (
  W Q2226868Angle A B C
) = if (
  (
    ( ( W Q2226868Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W Q2226868Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W Q2226868Ray A B )
        ( .i ` W )
        ( W Q2226868Ray C B )
      )
      /
      (
        ( W Q2226868Dist A B )
        x.
        ( W Q2226868Dist C B )
      )
    )
  )
) $.

${
  $d A B C W t $.

  q2226868-strict-between-definition $a |- (
    ( W Q2226868StrictBetween A B C )
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
  $d A B C D W $.

  thousand-theorems-q2226868-geometric-mean-theorem $a |- A. W
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
              (
                (
                  ( W Q2226868StrictBetween A D C )
                  /\
                  (
                    ( W Q2226868Angle A D B ) = ( _pi / 2 )
                    /\
                    ( W Q2226868Angle A B C ) = ( _pi / 2 )
                  )
                )
                ->
                (
                  ( ( W Q2226868Dist B D ) ^ 2 )
                  =
                  (
                    ( W Q2226868Dist A D )
                    x.
                    ( W Q2226868Dist C D )
                  )
                )
              )
    )
  $.
$}
