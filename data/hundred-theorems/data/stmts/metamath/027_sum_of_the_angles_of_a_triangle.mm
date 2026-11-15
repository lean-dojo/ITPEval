$(
  Statement-only formalization of "Sum of the Angles of a Triangle" from
  Hundred Theorems item 027: in an arbitrary real inner-product space, the
  three total unoriented vertex angles of a nontrivial triangle sum to pi.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The points are vectors in the carrier of a set.mm CPreHil structure whose
  scalar field is RRfld.  This is the vector-space presentation of the affine
  geometry used by the sources: W HT027Ray A B is A minus B.

  W HT027Angle A B C is the total unoriented angle at B.  It is pi/2 when
  either ray is zero, matching the total-angle convention in the source
  formulations; otherwise it is arccos of the real inner product divided by
  the product of the two norms.  Thus equality, real arithmetic, pi, arccos,
  the inner product, the norm, and the vector operations all have their
  definitions from set.mm.

  Metamath assertion variables are schematic, so W, A, B, and C are
  universally quantified subject to the displayed structure and carrier
  conditions.  The final declaration is the sole unproved geometric $a
  statement and is not a proof.
$)

$c HT027Ray HT027Angle $.

ht027-ray-syntax $a class ( W HT027Ray A B ) $.
ht027-angle-syntax $a class ( W HT027Angle A B C ) $.

ht027-ray-definition $a |- (
  W HT027Ray A B
) = (
  A ( -g ` W ) B
) $.

ht027-angle-definition $a |- (
  W HT027Angle A B C
) = if (
  (
    ( ( W HT027Ray A B ) = ( 0g ` W ) )
    \/
    ( ( W HT027Ray C B ) = ( 0g ` W ) )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      (
        ( W HT027Ray A B )
        ( .i ` W )
        ( W HT027Ray C B )
      )
      /
      (
        ( ( norm ` W ) ` ( W HT027Ray A B ) )
        x.
        ( ( norm ` W ) ` ( W HT027Ray C B ) )
      )
    )
  )
) $.

hundred-triangle-angle-sum $a |- (
  (
    W e. CPreHil
    /\
    (
      ( Scalar ` W ) = RRfld
      /\
      (
        A e. ( Base ` W )
        /\
        (
          B e. ( Base ` W )
          /\
          C e. ( Base ` W )
        )
      )
    )
  )
  ->
  (
    ( -. ( ( A = B ) /\ ( ( B = C ) /\ ( A = C ) ) ) )
    ->
    (
      (
        (
          ( W HT027Angle B A C )
          +
          ( W HT027Angle A B C )
        )
        +
        ( W HT027Angle B C A )
      )
      =
      _pi
    )
  )
) $.
