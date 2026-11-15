$(
  Statement-only formalization of Thousand Theorems corpus artifact Q877489
  (thousand-theorems__metamath__Q877489), "Apollonius's theorem": in an
  arbitrary real inner-product affine space, the sum of the squared distances
  from one point to two others equals twice the sum of the squared distance
  to their midpoint and the square of half their mutual distance. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces. The predicate
  W Q877489RealInnerProductSpace explicitly requires a generalized
  pre-Hilbert structure over RRfld, the normed-module laws, and the defining
  equality between the norm and the square root of the self inner product.
  It is therefore the SetMM rendering of the source NormedAddCommGroup and
  InnerProductSpace real typeclass package, without a finite-dimensionality
  restriction. Choosing any point as an affine origin identifies the source's
  normed affine torsor with Base ` W while preserving distances and affine
  midpoints; conversely, Base ` W is such a torsor.

  W Q877489Ray A B is the vector from B to A, W Q877489Dist A B is its norm,
  and W Q877489Mid B C is the affine midpoint of B and C.

  Every declaration before the final one is syntax or an explicit definition.
  The final $a declaration is the single unproved corpus statement, and this
  database contains no $p proof statement.
$)

$c Q877489RealInnerProductSpace Q877489Ray Q877489Dist Q877489Mid $.

q877489-real-inner-product-space-syntax
  $a wff ( W Q877489RealInnerProductSpace ) $.
q877489-ray-syntax $a class ( W Q877489Ray A B ) $.
q877489-distance-syntax $a class ( W Q877489Dist A B ) $.
q877489-midpoint-syntax $a class ( W Q877489Mid B C ) $.

${
  $d W x $.

  q877489-real-inner-product-space-definition $a |- (
    ( W Q877489RealInnerProductSpace )
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

q877489-ray-definition $a |- (
  W Q877489Ray A B
) = (
  A ( -g ` W ) B
) $.

q877489-distance-definition $a |- (
  W Q877489Dist A B
) = (
  ( norm ` W ) ` ( W Q877489Ray A B )
) $.

q877489-midpoint-definition $a |- (
  W Q877489Mid B C
) = (
  ( 1 / 2 )
  ( .s ` W )
  ( B ( +g ` W ) C )
) $.

${
  $d A B C W $.

  thousand-theorems-q877489-apollonius-theorem $a |- A. W
    (
      ( W Q877489RealInnerProductSpace )
      ->
      A. A e. ( Base ` W )
        A. B e. ( Base ` W )
          A. C e. ( Base ` W )
            (
              (
                ( ( W Q877489Dist A B ) ^ 2 )
                +
                ( ( W Q877489Dist A C ) ^ 2 )
              )
              =
              (
                2
                x.
                (
                  ( ( W Q877489Dist A ( W Q877489Mid B C ) ) ^ 2 )
                  +
                  ( ( ( W Q877489Dist B C ) / 2 ) ^ 2 )
                )
              )
            )
    )
  $.
$}
